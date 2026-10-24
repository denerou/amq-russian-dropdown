// ==UserScript==
// @name         AMQ Russian Dropdown
// @version      3.1.3
// @description
// @author       denero
// @match        https://animemusicquiz.com/*
// @match        https://www.animemusicquiz.com/*
// @updateURL    https://raw.githubusercontent.com/denerou/amq-russian-dropdown/main/amq-russian-dropdown.user.js
// @downloadURL  https://raw.githubusercontent.com/denerou/amq-russian-dropdown/main/amq-russian-dropdown.user.js
// @grant        GM_xmlhttpRequest
// @grant        unsafeWindow
// @connect      amq.mistnotalone.com
// @connect      shikimori.io
// @run-at       document-idle
// ==/UserScript==

(() => {
  "use strict";

  const API_BASE = "https://amq.mistnotalone.com";
  const SHIKIMORI_API_HOST = "shikimori.io";

  const SHIKIMORI_SEARCH_CACHE_TTL_MS = 10 * 60 * 1000;
  const SEARCH_DEBOUNCE_MS = 50;
  const AMQ_TITLES_CACHE_TTL_MS = 60 * 1000;
  const MAX_LISTENER_ATTEMPTS = 240;

  const SEARCH_CACHE_TTL_MS = 5 * 60 * 1000;
  const SEARCH_CACHE_MAX_ENTRIES = 300;
  const MAX_PATTERN_CACHE = 50;

  const TITLE_TRANSLITERATION_GROUPS = [
    ["си", "ши"], ["ти", "чи"], ["цу", "тсу"], ["дзи", "джи"], ["фу", "ху"],
    ["ся", "ша"], ["сю", "шу"], ["сё", "шо"], ["тя", "ча"], ["тю", "чу"],
    ["тё", "чо"], ["дзя", "джа"], ["дзю", "джу"], ["дзё", "джё"],
    ["мба", "нба"], ["мпа", "нпа"], ["мма", "нма"],
    ["нъа", "н-а"], ["нъи", "н-и"], ["нъя", "нья"], ["тти", "ччи"],
    ["й", "и"], ["йо", "ио", "ё"], ["дз", "з"], ["ё", "е"], ["cё", "шо"]
  ].sort((left, right) => right[0].length - left[0].length);

  const multipleChoiceTitleCache = new Map();
  const nameItemRussianTitleCache = new Map();
  const shikimoriSearchCache = new Map();
  const pendingShikimoriSearches = new Map();
  const confirmedDiscoveredMalIds = new Set();
  const searchResultCache = new Map();
  const compiledPatternCache = new Map();

  const annIdToMalIdMap = new Map();

  let amqTitlesCache = null;
  let amqTitlesCacheTimestamp = 0;
  let amqTitleIndexCache = null;
  let exactAmqTitleIndexCache = null;
  let amqExactStringIndexCache = null;

  function normalize(value) {
    return String(value || "")
      .toLowerCase()
      .normalize("NFKD")
      .replace(/[^\p{L}\p{N}]+/gu, " ")
      .trim()
      .replace(/\b(\d+)(?:st|nd|rd|th)\s+season\b/g, "season $1")
      .replace(/\s+/g, " ");
  }

  function normalizeAmqTitle(value) {
    return String(value || "")
      .toLowerCase()
      .replace(/\b(\d+)(?:st|nd|rd|th)\s+season\b/g, "season $1")
      .normalize("NFKC")
      .replace(/[\uFE00-\uFE0F\u{E0100}-\u{E01EF}]/gu, "")
      .normalize("NFKD")
      .replace(/\p{S}/gu, character =>
        ` unicode${character.codePointAt(0).toString(16)} `
      )
      .replace(/[^\p{L}\p{N}!*]+/gu, " ")
      .trim()
      .replace(/\s+/g, " ");
  }

  function buildFlexibleTitlePattern(query) {
    const characters = Array.from(String(query || "").trim().toLowerCase());
    let pattern = "";

    for (let index = 0; index < characters.length; index++) {
      const character = characters[index];
      const transliteration = getTitleTransliterationMatch(characters, index);
      if (transliteration) {
        pattern += `(?:${transliteration.alternatives
          .map(escapeRegExp)
          .join("|")})`;
        index += transliteration.length - 1;
        continue;
      }

      if (/\s/u.test(character)) {
        while (index + 1 < characters.length && /\s/u.test(characters[index + 1])) {
          index++;
        }
        pattern += "[\\s\\p{P}\\p{S}]+";
      } else {
        pattern += character.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
      }
    }

    return pattern;
  }

  function escapeRegExp(value) {
    return value.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
  }

  function getTitleTransliterationMatch(characters, index) {
    const character = characters[index];
    if (character === "е" || character === "э" || character === "ё") {
      return {
        length: 1,
        alternatives: [...new Set([character, "е", "э", "ё"])]
      };
    }

    for (const group of TITLE_TRANSLITERATION_GROUPS) {
      const matched = group.find(value =>
        characters.slice(index, index + value.length).join("") === value
      );
      if (matched) return { length: matched.length, alternatives: group };
    }
    return null;
  }

  function getTitleTransliterationVariants(value, limit = 8) {
    const initial = String(value || "").trim().toLowerCase();
    const variants = new Set([initial]);
    const queue = [initial];

    while (queue.length && variants.size < limit) {
      const current = queue.shift();
      const characters = Array.from(current);

      for (let index = 0; index < characters.length; index++) {
        const match = getTitleTransliterationMatch(characters, index);
        if (!match) continue;

        const changedLength = match.length;
        for (const alternative of match.alternatives) {
          if (characters.slice(index, index + changedLength).join("") === alternative) {
            continue;
          }
          const candidate = [
            ...characters.slice(0, index),
            ...Array.from(alternative),
            ...characters.slice(index + changedLength)
          ].join("");
          if (!variants.has(candidate) && variants.size < limit) {
            variants.add(candidate);
            queue.push(candidate);
          }
        }
      }
    }

    return [...variants];
  }

  function getCompiledPattern(query) {
    const key = String(query || "").trim().toLowerCase();
    if (!key) return null;
    const cached = compiledPatternCache.get(key);
    if (cached) return cached;
    const re = new RegExp(buildFlexibleTitlePattern(key), "iu");
    if (compiledPatternCache.size >= MAX_PATTERN_CACHE) {
      compiledPatternCache.delete(compiledPatternCache.keys().next().value);
    }
    compiledPatternCache.set(key, re);
    return re;
  }

  function findTitleMatches(title, query) {
    const re = getCompiledPattern(query);
    if (!re) return false;
    return re.test(title);
  }

  function getCandidateSearchQueries(query) {
    const words = String(query || "")
      .toLowerCase()
      .match(/[\p{L}\p{N}]+/gu) || [];
    const longestWords = [...new Set(words.filter(word => word.length >= 2))]
      .sort((left, right) => right.length - left.length)
      .slice(0, 3);
    const queries = new Set(getTitleTransliterationVariants(query));
    for (const word of longestWords) {
      queries.add(word);
      for (const variant of getTitleTransliterationVariants(word)) {
        queries.add(variant);
      }
    }
    return [...queries].filter(candidate => candidate.length >= 2).slice(0, 8);
  }

  function mergeAnimeResults(responses) {
    const animes = new Map();
    for (const response of responses) {
      if (!Array.isArray(response)) continue;
      for (const anime of response) {
        if (!anime?.russian || !anime?.name) continue;
        const key =
          `${normalizeAmqTitle(anime.russian)}\u0000${normalizeAmqTitle(anime.name)}`;
        const current = animes.get(key);
        if (!current) {
          animes.set(key, anime);
        } else {
          animes.set(key, {
            ...current,
            ...anime,
            titlePriority: Math.max(
              Number(current.titlePriority) || 0,
              Number(anime.titlePriority) || 0
            )
          });
        }
      }
    }
    return [...animes.values()];
  }

  function hasUsableSearchMatch(animes, query) {
    return animes.some(anime => {
      if (!anime?.russian || !anime?.name) return false;
      const namesToCheck = [
        anime.russian,
        ...(Array.isArray(anime.russianAliases) ? anime.russianAliases : []),
        ...(Array.isArray(anime.synonyms) ? anime.synonyms : [])
      ];
      return namesToCheck.some(name => typeof name === "string" && findTitleMatches(name, query));
    });
  }

  function getAmqTitleMatchesForAnime(anime) {
    const exactStringIndex = getAmqExactStringIndex();
    const exactTitleIndex = getExactAmqTitleIndex();
    const titleGroups = [
      {
        priority: 3,
        names: [
          ...(Array.isArray(anime?.romajiTitles) ? anime.romajiTitles : []),
          anime?.name,
          ...(Array.isArray(anime?.japanese) ? anime.japanese : [])
        ]
      },
      {
        priority: 2,
        names: [
          ...(Array.isArray(anime?.englishTitles) ? anime.englishTitles : []),
          ...(Array.isArray(anime?.english) ? anime.english : [])
        ]
      },
      {
        priority: 1,
        names: Array.isArray(anime?.synonyms) ? anime.synonyms : []
      }
    ];
    const matches = new Map();
    for (const group of titleGroups) {
      for (const name of group.names) {
        if (typeof name !== "string") continue;

        const exactStringMatch = exactStringIndex?.get(name.toLowerCase());
        if (exactStringMatch) {
          const key = normalizeAmqTitle(exactStringMatch.value);
          const current = matches.get(key);
          if (!current || group.priority > current.priority || (group.priority === current.priority && exactStringMatch.value.length > current.value.length)) {
            matches.set(key, { ...exactStringMatch, priority: group.priority });
          }
          continue;
        }

        const exactMatch = exactTitleIndex?.get(normalizeAmqTitle(name));
        if (exactMatch) {
          const key = normalizeAmqTitle(exactMatch.value);
          const current = matches.get(key);
          if (!current || group.priority > current.priority || (group.priority === current.priority && exactMatch.value.length > current.value.length)) {
            matches.set(key, { ...exactMatch, priority: group.priority });
          }
        }
      }
    }
    const sortedMatches = [...matches.values()].sort(
      (left, right) =>
        right.priority - left.priority ||
        right.value.length - left.value.length
    );
    return sortedMatches.length ? [sortedMatches[0]] : [];
  }

  function getAmqTitleMatchForAnime(anime) {
    return getAmqTitleMatchesForAnime(anime)[0] || null;
  }

  function requestShikimoriSearchCandidates(query) {
    const cacheKey = query.trim().toLowerCase();
    const cached = shikimoriSearchCache.get(cacheKey);
    if (cached && cached.expiresAt > Date.now()) {
      return Promise.resolve(cached.results);
    }
    if (pendingShikimoriSearches.has(cacheKey)) {
      return pendingShikimoriSearches.get(cacheKey);
    }
    const search = (async () => {
      const searchTerms = getTitleTransliterationVariants(query);
      const candidates = new Map();
      let lastError;
      const collectCandidates = response => {
        if (!Array.isArray(response)) {
          throw new Error("Shikimori search response is not an array");
        }
        for (const anime of response) {
          if (!Number.isSafeInteger(anime?.id)) continue;
          const namesToCheck = [
            anime.russian,
            anime.name,
            ...(Array.isArray(anime.synonyms) ? anime.synonyms : [])
          ].filter(n => typeof n === "string");
          if (namesToCheck.some(name => findTitleMatches(name, query))) {
            candidates.set(anime.id, anime);
          }
        }
      };
      const requestSearchTerm = async term => {
        const searchUrl = new URL(`https://${SHIKIMORI_API_HOST}/api/animes`);
        searchUrl.searchParams.set("search", term);
        searchUrl.searchParams.set("limit", "50");
        return requestJsonWithRetry(searchUrl.href, undefined);
      };
      try {
        collectCandidates(await requestSearchTerm(searchTerms[0]));
      } catch (error) {
        lastError = error;
      }
      if (!candidates.size) {
        for (let index = 1; index < searchTerms.length; index += 4) {
          if (index > 1) {
            await new Promise(resolve => setTimeout(resolve, 300));
          }
          const responses = await Promise.allSettled(
            searchTerms
              .slice(index, index + 4)
              .map(requestSearchTerm)
          );
          for (const response of responses) {
            if (response.status === "rejected") {
              lastError = response.reason;
              continue;
            }
            try {
              collectCandidates(response.value);
            } catch (error) {
              lastError = error;
            }
          }
        }
      }
      if (!candidates.size && lastError) throw lastError;
      const results = [];
      const detailCandidates = [...candidates.values()].slice(0, 6);
      const detailResponses = await Promise.allSettled(
        detailCandidates.map(candidate =>
          requestJsonWithRetry(
            `https://${SHIKIMORI_API_HOST}/api/animes/${candidate.id}`,
            undefined
          )
        )
      );
      for (const response of detailResponses) {
        if (response.status === "rejected") {
          lastError = response.reason;
          continue;
        }
        const anime = extractShikimoriAnime(response.value);
        if (!anime || typeof anime.russian !== "string") {
          continue;
        }
        const detailNamesToCheck = [
          anime.russian,
          anime.name,
          ...(Array.isArray(anime.synonyms) ? anime.synonyms : [])
        ].filter(n => typeof n === "string");
        if (!detailNamesToCheck.some(name => findTitleMatches(name, query))) {
          continue;
        }
        const amqTitles = getAmqTitleMatchesForAnime(anime);
        const malId = Number(anime.myanimelist_id);
        if (!amqTitles.length || !Number.isSafeInteger(malId) || malId < 1) continue;
        for (const amqTitle of amqTitles) {
          results.push({
            id: malId,
            malId,
            name: amqTitle.value,
            amqTitle: amqTitle.label,
            russian: anime.russian.trim(),
            titlePriority: amqTitle.priority
          });
        }
      }
      if (!results.length && lastError) throw lastError;
      shikimoriSearchCache.set(cacheKey, {
        results,
        expiresAt: Date.now() + SHIKIMORI_SEARCH_CACHE_TTL_MS
      });
      return results;
    })().finally(() => pendingShikimoriSearches.delete(cacheKey));
    pendingShikimoriSearches.set(cacheKey, search);
    return search;
  }

  async function persistDiscoveredShikimoriTitle(candidate, query) {
    const malId = Number(candidate.malId);
    const amqTitle =
      typeof candidate.name === "string" ? candidate.name.trim() : "";
    const russianTitle =
      typeof candidate.russian === "string" ? candidate.russian.trim() : "";
    if (
      !Number.isSafeInteger(malId) ||
      malId < 1 ||
      !russianTitle ||
      !findTitleMatches(russianTitle, query)
    ) {
      return;
    }
    if (confirmedDiscoveredMalIds.has(malId)) return;
    const response = await requestJsonWithRetry(
      `${API_BASE}/api/discovered-title`,
      {
        method: "POST",
        body: JSON.stringify({ query, malId, amqTitle })
      }
    );
    if (!response?.ok) {
      throw new Error(`API did not confirm saving MAL ID ${malId}`);
    }
    confirmedDiscoveredMalIds.add(malId);
  }

  function persistDiscoveredShikimoriTitles(
    candidates,
    query,
    databaseResults
  ) {
    const databaseRussianTitles = new Set(
      databaseResults.map(anime => normalizeAmqTitle(anime.russian))
    );
    const uniqueCandidates = new Map();
    for (const candidate of candidates) {
      if (
        Number.isSafeInteger(candidate?.malId) &&
        !databaseRussianTitles.has(normalizeAmqTitle(candidate.russian))
      ) {
        uniqueCandidates.set(candidate.malId, candidate);
      }
    }
    void (async () => {
      for (const candidate of uniqueCandidates.values()) {
        try {
          await persistDiscoveredShikimoriTitle(candidate, query);
        } catch (error) {
          console.debug(
            "[AMQ Russian Dropdown] Could not persist discovered title",
            { malId: candidate.malId, error }
          );
        }
      }
    })();
  }

  function requestCachedSearch(candidate) {
    const key = candidate.trim().toLowerCase();
    const cached = searchResultCache.get(key);
    if (cached && cached.expiresAt > Date.now()) {
      return Promise.resolve(cached.results);
    }
    return requestJson(
      `${API_BASE}/api/search?q=${encodeURIComponent(candidate)}`
    ).then(results => {
      if (searchResultCache.size >= SEARCH_CACHE_MAX_ENTRIES) {
        const oldest = [...searchResultCache.entries()]
          .sort((a, b) => a[1].expiresAt - b[1].expiresAt)[0];
        if (oldest) searchResultCache.delete(oldest[0]);
      }
      searchResultCache.set(key, {
        results,
        expiresAt: Date.now() + SEARCH_CACHE_TTL_MS
      });
      return results;
    });
  }

  function tryShikimoriInBackground(query, databaseResults, onDatabaseResults) {
    requestShikimoriSearchCandidates(query)
      .then(shikimoriResults => {
        if (!shikimoriResults.length) return;
        onDatabaseResults(
          mergeAnimeResults([databaseResults, shikimoriResults])
        );
        persistDiscoveredShikimoriTitles(
          shikimoriResults,
          query,
          databaseResults
        );
      })
      .catch(error => {
        console.debug(
          "[AMQ Russian Dropdown] Background Shikimori search failed",
          error
        );
      });
  }

  async function requestSearchCandidates(query, onDatabaseResults) {
    const requestCandidate = candidate => requestCachedSearch(candidate);
    let databaseResults = [];
    let shikimoriResults = [];
    const publishResults = () => {
      const results = mergeAnimeResults([databaseResults, shikimoriResults]);
      if (results.length) {
        onDatabaseResults(results);
      }
    };
    let directResults = [];
    let directError;
    try {
      directResults = await requestCandidate(query);
    } catch (error) {
      directError = error;
    }
    const mergedDirectResults = mergeAnimeResults([directResults]);
    databaseResults = mergedDirectResults;
    publishResults();

    if (hasUsableSearchMatch(mergedDirectResults, query)) {
      tryShikimoriInBackground(query, databaseResults, onDatabaseResults);
      return mergedDirectResults;
    }

    const fallbackQueries = getCandidateSearchQueries(query)
      .filter(candidate => candidate !== query.trim());

    let anyFallbackSuccess = false;
    await Promise.allSettled(
      fallbackQueries.map(candidate =>
        requestCandidate(candidate)
          .then(results => {
            if (Array.isArray(results) && results.length) {
              anyFallbackSuccess = true;
              databaseResults = mergeAnimeResults([
                databaseResults,
                results
              ]);
              publishResults();
            }
          })
          .catch(() => {})
      )
    );

    if (hasUsableSearchMatch(databaseResults, query)) {
      tryShikimoriInBackground(query, databaseResults, onDatabaseResults);
      return databaseResults;
    }

    try {
      shikimoriResults = await requestShikimoriSearchCandidates(query);
    } catch (error) {
      if (directError && !anyFallbackSuccess) throw directError;
      return databaseResults;
    }

    if (
      directError &&
      !anyFallbackSuccess &&
      shikimoriResults.length === 0
    ) {
      throw directError;
    }
    persistDiscoveredShikimoriTitles(
      shikimoriResults,
      query,
      databaseResults
    );
    return mergeAnimeResults([databaseResults, shikimoriResults]);
  }

  function getAmqTitles() {
    const now = Date.now();
    if (
      amqTitlesCache &&
      now - amqTitlesCacheTimestamp < AMQ_TITLES_CACHE_TTL_MS
    ) {
      return amqTitlesCache;
    }
    const list =
      unsafeWindow.quiz?.answerInput?.typingInput?.autoCompleteController?.list;
    if (!Array.isArray(list) || !list.length) return [];
    amqTitlesCache = list
      .map(item => {
        if (typeof item === "string") {
          return { value: item, label: item };
        }
        const value =
          item?.value ??
          item?.label ??
          item?.name ??
          item?.title ??
          item?.animeName ??
          "";
        const label = item?.label ?? value;
        return {
          value: String(value).trim(),
          label: String(label).trim()
        };
      })
      .filter(item => item.value);
    amqTitlesCacheTimestamp = now;
    amqTitleIndexCache = null;
    exactAmqTitleIndexCache = null;
    amqExactStringIndexCache = null;
    return amqTitlesCache;
  }

  function getAmqTitleIndex() {
    if (amqTitleIndexCache) return amqTitleIndexCache;
    const titles = getAmqTitles();
    if (!titles.length) return null;
    const index = new Map();
    for (const item of titles) {
      const key = normalize(item.value);
      if (key && !index.has(key)) {
        index.set(key, item);
      }
    }
    amqTitleIndexCache = index;
    return amqTitleIndexCache;
  }

  function getExactAmqTitleIndex() {
    if (exactAmqTitleIndexCache) return exactAmqTitleIndexCache;
    const titles = getAmqTitles();
    if (!titles.length) return null;
    const index = new Map();
    for (const item of titles) {
      const key = normalizeAmqTitle(item.value);
      if (key && !index.has(key)) index.set(key, item);
    }
    exactAmqTitleIndexCache = index;
    return exactAmqTitleIndexCache;
  }

  function getAmqExactStringIndex() {
    if (amqExactStringIndexCache) return amqExactStringIndexCache;
    const titles = getAmqTitles();
    if (!titles.length) return null;
    const index = new Map();
    for (const item of titles) {
      const key = item.value.toLowerCase();
      if (key && !index.has(key)) index.set(key, item);
    }
    amqExactStringIndexCache = index;
    return amqExactStringIndexCache;
  }

  function requestJson(url, options = {}) {
    return new Promise((resolve, reject) => {
      GM_xmlhttpRequest({
        method: options.method || "GET",
        url,
        headers: {
          Accept: "application/json",
          ...(options.body ? { "Content-Type": "application/json" } : {})
        },
        data: options.body,
        timeout: 8000,
        onload(response) {
          if (response.status < 200 || response.status >= 300) {
            const error = new Error(
              `${new URL(url).hostname} returned HTTP ${response.status}`
            );
            error.statusCode = response.status;
            reject(error);
            return;
          }
          try {
            resolve(JSON.parse(response.responseText));
          } catch (error) {
            reject(error);
          }
        },
        onerror() {
          reject(new Error(`Could not connect to ${new URL(url).hostname}`));
        },
        ontimeout() {
          reject(new Error(`Request timed out for ${new URL(url).hostname}`));
        }
      });
    });
  }

  async function requestJsonWithRetry(url, options, maxAttempts = 2) {
    for (let attempt = 1; ; attempt++) {
      try {
        return await requestJson(url, options);
      } catch (error) {
        const retryable =
          error.statusCode === 429 ||
          (error.statusCode >= 500 && error.statusCode <= 599);
        if (!retryable || attempt >= maxAttempts) throw error;
        await new Promise(resolve => setTimeout(resolve, 500 * attempt));
      }
    }
  }

  function extractShikimoriAnime(response) {
    return Array.isArray(response) ? response[0] : response;
  }

  function requestNameItemRussianTitle(annId, malId) {
    if (!annId && !malId) {
      return Promise.reject(new Error("No IDs provided"));
    }
    const cacheKey = malId ? `mal:${malId}` : `ann:${annId}`;
    if (nameItemRussianTitleCache.has(cacheKey)) {
      return nameItemRussianTitleCache.get(cacheKey);
    }
    const url = new URL(`${API_BASE}/api/name-item`);
    if (annId) url.searchParams.set("annId", String(annId));
    if (malId) url.searchParams.set("malId", String(malId));

    const lookup = requestJson(url.href).then(response => {
      if (
        (response?.malId !== undefined && response?.malId !== malId) ||
        (response?.annId !== undefined && response?.annId !== annId) ||
        (response?.animeRussian !== null && typeof response?.animeRussian !== "string") ||
        !Array.isArray(response?.russianAliases) ||
        response.russianAliases.some(alias => typeof alias !== "string")
      ) {
        throw new Error("Name item title API returned an invalid response");
      }
      return {
        animeRussian: response.animeRussian?.trim() || null,
        russianAliases: response.russianAliases
          .map(alias => alias.trim())
          .filter((alias, index, aliases) =>
            alias && aliases.indexOf(alias) === index
          )
      };
    });
    nameItemRussianTitleCache.set(cacheKey, lookup);
    lookup.catch(() => nameItemRussianTitleCache.delete(cacheKey));
    return lookup;
  }

  const COLORS = {
    variables: {
      textColor: "--textColor",
      panelBackground: "--primaryColor",
      accentColor: "--accentColor"
    },
    fallback: {
      textColor: "#f4f4f4",
      panelBackground: "#202124",
      accentColor: "#c084fc"
    },
    current: {
      textColor: "#f4f4f4",
      panelBackground: "#202124",
      accentColor: "#c084fc"
    }
  };

  const panel = document.createElement("div");
  panel.id = "amqRussianTitlePanel";
  panel.className = "amqRussianTitlePanel";

  const viewport = document.createElement("div");
  viewport.id = "amqRussianListViewport";
  viewport.className = "amqRussianListViewport";

  const scrollbarTrack = document.createElement("div");
  scrollbarTrack.id = "amqRussianScrollbarTrack";

  const scrollbarThumb = document.createElement("div");
  scrollbarThumb.id = "amqRussianScrollbarThumb";
  scrollbarTrack.appendChild(scrollbarThumb);

  panel.append(viewport, scrollbarTrack);

  let activeAnswerTitleRequest = 0;
  let answerRussianTitleListenerBound = false;

  let debounceTimer;
  let requestId = 0;
  let keyboardIndex = -1;
  let mouseIndex = -1;
  let currentResults = [];
  let dragStartY = 0;
  let dragStartScrollTop = 0;
  let answerRound = 0;
  let selectionGeneration = 0;
  let lastQuery = "";
  let lastRenderedRequestId = -1;
  let lastRenderedQuery = "";

  function setAnswerRussianTitle(tooltip, animeRussian, aliases = []) {
    const content = tooltip.querySelector(".amqAnswerRussianTitleText");
    if (!content) return;

    content.replaceChildren();
    const lines = [
      animeRussian || "Русское название не найдено в базе",
      ...aliases
    ];
    lines.forEach((line, index) => {
      if (index) content.appendChild(document.createElement("br"));
      content.appendChild(document.createTextNode(line));
    });
  }

  function showAnswerRussianTitleTooltip(container, tooltip) {
    tooltip.style.display = "flex";
    const containerRect = container.getBoundingClientRect();
    const tooltipRect = tooltip.getBoundingClientRect();
    const viewportPadding = 8;
    const minCenter = viewportPadding + tooltipRect.height / 2;
    const maxCenter = window.innerHeight - viewportPadding - tooltipRect.height / 2;
    const center = Math.min(
      Math.max(containerRect.top + containerRect.height / 2, minCenter),
      Math.max(minCenter, maxCenter)
    );
    tooltip.style.top = `${center - containerRect.top}px`;

    const arrow = tooltip.querySelector(".amqAnswerRussianTitleArrow");
    if (arrow) {
      const positionedTooltipRect = tooltip.getBoundingClientRect();
      const arrowCenter = containerRect.top + containerRect.height / 2;
      const arrowOffset = Math.min(
        Math.max(arrowCenter - positionedTooltipRect.top, 12),
        positionedTooltipRect.height - 12
      );
      arrow.style.top = `${arrowOffset}px`;
    }
  }

  function ensureAnswerRussianTitleTooltip(container) {
    const tooltipClass = "amqAnswerRussianTitle";
    let tooltip = container.querySelector(`.${tooltipClass}`);
    if (tooltip) return tooltip;
    tooltip = document.createElement("div");
    tooltip.className = tooltipClass;
    tooltip.setAttribute("role", "status");
    const content = document.createElement("span");
    content.className = "amqAnswerRussianTitleText";
    const arrow = document.createElement("div");
    arrow.className = "amqAnswerRussianTitleArrow";
    arrow.setAttribute("aria-hidden", "true");
    tooltip.append(content, arrow);
    if (getComputedStyle(container).position === "static") {
      container.classList.add("amqRussianPositioned");
    }
    container.appendChild(tooltip);
    container.addEventListener("mouseenter", () => {
      if (content.textContent.trim()) {
        showAnswerRussianTitleTooltip(container, tooltip);
      }
    });
    container.addEventListener("mouseleave", () => {
      tooltip.style.display = "none";
    });
    return tooltip;
  }

  function handleAnswerResults(data) {
    answerRound++;
    hidePanel();

    const annId = Number(data?.songInfo?.siteIds?.annId);
    const malId = Number(data?.songInfo?.siteIds?.malId);

    if (Number.isSafeInteger(annId) && annId > 0 && Number.isSafeInteger(malId) && malId > 0) {
      annIdToMalIdMap.set(annId, malId);
    }

    const currentRequest = ++activeAnswerTitleRequest;
    const container = document.querySelector("#qpAnimeNameContainer");
    if (!container || (!Number.isSafeInteger(malId) && !Number.isSafeInteger(annId))) return;

    const tooltip = ensureAnswerRussianTitleTooltip(container);

    const content = tooltip.querySelector(".amqAnswerRussianTitleText");
    if (content) content.textContent = "";
    tooltip.style.display = "none";

    requestNameItemRussianTitle(annId, malId)
      .then(result => {
        if (currentRequest !== activeAnswerTitleRequest || !container.isConnected) {
          return;
        }
        setAnswerRussianTitle(
          tooltip,
          result.animeRussian,
          result.russianAliases
        );
        if (container.matches(":hover")) {
          showAnswerRussianTitleTooltip(container, tooltip);
        }
      })
      .catch(error => {
        if (currentRequest !== activeAnswerTitleRequest) return;
        setAnswerRussianTitle(tooltip, `Ошибка загрузки: ${error.message}`);
        if (container.matches(":hover")) {
          showAnswerRussianTitleTooltip(container, tooltip);
        }
      });
  }

  function setupAnswerRussianTitleListener() {
    if (answerRussianTitleListenerBound || typeof Listener !== "function") {
      return answerRussianTitleListenerBound;
    }
    new Listener("answer results", handleAnswerResults).bindListener();
    answerRussianTitleListenerBound = true;
    return true;
  }

  function getSongHistoryIds(container) {
    let annId = null;
    let malId = null;

    const malAnchor = container.querySelector(
      "a[href*='myanimelist.net/anime/']"
    );
    if (malAnchor) {
      const hrefMatch = malAnchor.href.match(/myanimelist\.net\/anime\/(\d+)/i);
      const textMatch = malAnchor.textContent.match(/\d+/);
      const parsed = Number(hrefMatch?.[1] || textMatch?.[0]);
      if (Number.isSafeInteger(parsed) && parsed > 0) malId = parsed;
    }

    const annAnchor = container.querySelector(
      "a[href*='animenewsnetwork.com/encyclopedia/anime.php?id=']"
    );
    if (annAnchor) {
      const hrefMatch = annAnchor.href.match(/id=(\d+)/i);
      const textMatch = annAnchor.textContent.match(/\d+/);
      const parsed = Number(hrefMatch?.[1] || textMatch?.[0]);
      if (Number.isSafeInteger(parsed) && parsed > 0) annId = parsed;
    }

    if (annId && annIdToMalIdMap.has(annId)) {
      if (!malId) malId = annIdToMalIdMap.get(annId);
    }

    return { annId, malId };
  }

  function ensureSongHistoryRussianEntry(container) {
    const entries = [...container.querySelectorAll("#shiAnimeRussianTitle")];
    const existingValue = entries.shift() || null;
    for (const duplicate of entries) {
      duplicate.closest(".shiEntry")?.remove();
    }
    if (existingValue) {
      const row = existingValue.closest(".shiEntry");
      if (row && container.firstElementChild !== row) {
        container.prepend(row);
      }
      return existingValue;
    }

    const row = document.createElement("div");
    row.className = "shiEntry";
    const label = document.createElement("div");
    label.className = "shiEntryTitle";
    label.setAttribute(
      "data-i18n",
      "song_history.song_window.anime_russian"
    );
    label.textContent = "Anime Russian";
    const value = document.createElement("div");
    value.className = "shiEntryValue";
    value.id = "shiAnimeRussianTitle";
    row.append(label, value);
    container.prepend(row);
    return value;
  }

  function updateSongHistoryRussianTitles() {
    const containers = [...document.querySelectorAll(".shiEntryContainer")];
    if (!containers.length) return;

    const allIds = containers.map(getSongHistoryIds);
    const ids = {
      annId: allIds.find(i => i.annId)?.annId || null,
      malId: allIds.find(i => i.malId)?.malId || null
    };

    if (!ids.annId && !ids.malId) {
      document.querySelectorAll("#shiAnimeRussianTitle").forEach(el => el.closest(".shiEntry").remove());
      document.querySelectorAll("[data-amq-russian-title], [data-amq-russian-alias]").forEach(el => el.remove());
      if (containers[0]) delete containers[0].dataset.amqLoadedMal;
      if (containers[2]) delete containers[2].dataset.amqLoadedMal;
      return;
    }

    const lookupKey = ids.malId ? `mal:${ids.malId}` : `ann:${ids.annId}`;
    const mainContainer = containers[0];
    const targetContainer = containers[2];

    const isMainLoaded = mainContainer && mainContainer.querySelector("#shiAnimeRussianTitle")?.dataset.loadedMal === lookupKey;
    const targetEntry = targetContainer ? targetContainer.querySelector(".shiEntry") : null;
    const isTargetLoaded = targetEntry && targetEntry.dataset.amqTargetLoadedMal === lookupKey;

    if (isMainLoaded && isTargetLoaded) return;

    if (mainContainer) {
      const mainValue = ensureSongHistoryRussianEntry(mainContainer);
      const label = mainValue.parentElement?.querySelector(
        '[data-i18n="song_history.song_window.anime_russian"]'
      );
      const languageText = document.querySelector("#smLanguageCurrentText")?.textContent.trim() || "";
      const labelText = languageText === "Русский язык" ? "Название (рус.)" : "Anime Russian";
      if (label && label.textContent !== labelText) label.textContent = labelText;

      if (mainValue.dataset.loadedMal !== lookupKey) {
        if (mainValue.textContent !== "Загрузка…") mainValue.textContent = "Загрузка…";
      }
    }

    let targetMultiRow = null;
    if (targetEntry) {
      targetMultiRow = targetEntry.querySelector(".shiEntryMultiRow");
      if (!targetMultiRow) {
        targetMultiRow = document.createElement("div");
        targetMultiRow.className = "shiEntryMultiRow";
        targetEntry.appendChild(targetMultiRow);
      }
    }

    if (mainContainer) {
      const mainValue = mainContainer.querySelector("#shiAnimeRussianTitle");
      if (mainValue && mainValue.dataset.isLoading === "true" && mainValue.dataset.loadingMal === lookupKey) {
        return;
      }
      if (mainValue) {
        mainValue.dataset.isLoading = "true";
        mainValue.dataset.loadingMal = lookupKey;
      }
    }

    requestNameItemRussianTitle(ids.annId, ids.malId)
      .then(result => {
        if (mainContainer) {
          const mainValue = mainContainer.querySelector("#shiAnimeRussianTitle");
          if (mainValue) {
            mainValue.dataset.isLoading = "false";
            mainValue.dataset.loadedMal = lookupKey;
            mainValue.textContent = result.animeRussian || "Нет в базе";
          }
        }

        if (targetEntry && targetMultiRow) {
          targetEntry.dataset.amqTargetLoadedMal = lookupKey;
          targetMultiRow.querySelectorAll("[data-amq-russian-title], [data-amq-russian-alias]").forEach(el => el.remove());

          if (result.animeRussian) {
            const div = document.createElement("div");
            div.className = "shiEntryValue";
            div.dataset.amqRussianTitle = "true";
            div.textContent = result.animeRussian;
            targetMultiRow.appendChild(div);
          }

          for (const alias of result.russianAliases) {
            const div = document.createElement("div");
            div.className = "shiEntryValue";
            div.dataset.amqRussianAlias = "true";
            div.textContent = alias;
            targetMultiRow.appendChild(div);
          }
        }
      })
      .catch(error => {
        if (mainContainer) {
          const mainValue = mainContainer.querySelector("#shiAnimeRussianTitle");
          if (mainValue) {
            mainValue.dataset.isLoading = "false";
            mainValue.textContent = "Ошибка загрузки";
          }
        }
        console.error("[AMQ Russian Dropdown] Could not load titles:", error);
      });
  }

  function getMultipleChoiceSourceTitle(entry, textElement) {
    return (
      entry.getAttribute("data-original-title") ||
      entry.getAttribute("title") ||
      textElement.textContent.trim()
    ).trim();
  }

  function requestMultipleChoiceRussianTitle(amqTitle) {
    if (multipleChoiceTitleCache.has(amqTitle)) {
      return multipleChoiceTitleCache.get(amqTitle);
    }
    const url = new URL(`${API_BASE}/api/title-translation`);
    url.searchParams.set("title", amqTitle);
    const lookup = requestJson(url.href)
      .then(response => {
        if (
          response?.russian !== null &&
          typeof response?.russian !== "string"
        ) {
          throw new Error("Title translation API returned an invalid response");
        }
        return response.russian?.trim() || null;
      })
      .catch(error => {
        console.warn(
          `[AMQ Russian Dropdown] Could not translate multiple-choice title "${amqTitle}".`,
          error
        );
        return null;
      });
    multipleChoiceTitleCache.set(amqTitle, lookup);
    return lookup;
  }

  function translateMultipleChoiceTitles(root) {
    for (const entry of root.querySelectorAll(".qpMultipleChoiceEntryContainer")) {
      const textElement = entry.querySelector(".qpMultipleChoiceEntryText");
      if (!textElement) continue;
      const sourceTitle = getMultipleChoiceSourceTitle(entry, textElement);
      if (!sourceTitle) continue;
      if (
        textElement.dataset.amqRussianTitleSource === sourceTitle &&
        textElement.textContent.trim() !== sourceTitle
      ) {
        continue;
      }
      textElement.dataset.amqRussianTitleSource = sourceTitle;
      void requestMultipleChoiceRussianTitle(sourceTitle).then(russianTitle => {
        if (
          !russianTitle ||
          !entry.isConnected ||
          !textElement.isConnected ||
          getMultipleChoiceSourceTitle(entry, textElement) !== sourceTitle
        ) {
          return;
        }
        textElement.textContent = russianTitle;
      });
    }
  }

  function setupMultipleChoiceTitleTranslation() {
    const container = document.querySelector("#qpMultipleChoiceContainer");
    if (!container) return false;
    if (container.dataset.amqRussianTitleObserver) return true;
    container.dataset.amqRussianTitleObserver = "true";
    const observer = new MutationObserver(() => {
      translateMultipleChoiceTitles(container);
    });
    observer.observe(container, {
      childList: true,
      subtree: true,
      characterData: true,
      attributes: true,
      attributeFilter: ["data-original-title", "title"]
    });
    translateMultipleChoiceTitles(container);
    return true;
  }

  function getInput() {
    return document.querySelector("#qpAnswerInput");
  }

  function updateColors(input) {
    const nativeList = document.querySelector(
      "#qpAnswerInputContainer .awesomplete ul"
    );
    const selectedOption = nativeList?.querySelector(
      "li[aria-selected='true'], li:hover"
    );
    const variableElements = [];
    for (let element = input; element; element = element.parentElement) {
      variableElements.push(element);
    }
    if (document.body) variableElements.push(document.body);
    if (document.documentElement) variableElements.push(document.documentElement);
    function findColor(candidates) {
      for (const [element, property] of candidates) {
        if (!element) continue;
        const color = getComputedStyle(element)[property].trim();
        if (color && color !== "transparent" && color !== "rgba(0, 0, 0, 0)") {
          return color;
        }
      }
      return "";
    }
    for (const [key, variable] of Object.entries(COLORS.variables)) {
      let value = "";
      for (const element of variableElements) {
        value = getComputedStyle(element).getPropertyValue(variable).trim();
        if (value) break;
      }
      const candidates =
        key === "textColor"
          ? [[input, "color"], [nativeList, "color"], [selectedOption, "color"]]
          : key === "panelBackground"
            ? [[nativeList, "backgroundColor"], [input, "backgroundColor"]]
            : [
                [selectedOption, "backgroundColor"],
                [document.querySelector(".btn-primary"), "backgroundColor"],
                [input, "borderColor"]
              ].filter(([element]) => element);
      COLORS.current[key] =
        value || findColor(candidates) || COLORS.fallback[key];
    }
    panel.style.setProperty(
      "--amq-russian-accent",
      COLORS.current.accentColor
    );
  }

  function positionPanel() {
    const input = getInput();
    const wrapper = document.querySelector(
      "#qpAnswerInputContainer .awesomplete"
    );
    if (!input || !wrapper) return;
    updateColors(input);
    if (getComputedStyle(wrapper).position === "static") {
      wrapper.classList.add("amqRussianPositioned");
    }
    if (panel.parentElement !== wrapper) {
      wrapper.appendChild(panel);
    }
    panel.style.left = "0";
    panel.style.top = `${input.offsetHeight}px`;
    panel.style.width = `${wrapper.getBoundingClientRect().width}px`;
    panel.style.font = getComputedStyle(input).font;
    panel.style.backgroundColor = COLORS.current.panelBackground;
    panel.style.color = COLORS.current.textColor;
    updateScrollbar();
  }

  function updateScrollbar() {
    const visibleHeight = viewport.clientHeight;
    const contentHeight = viewport.scrollHeight;
    const trackHeight = scrollbarTrack.clientHeight;
    if (!visibleHeight || !trackHeight || contentHeight <= visibleHeight) {
      scrollbarThumb.style.display = "none";
      return;
    }
    scrollbarThumb.style.display = "block";
    const thumbHeight = Math.max(
      20,
      trackHeight * (visibleHeight / contentHeight) * 0.25
    );
    const maxThumbTop = trackHeight - thumbHeight;
    const maxScrollTop = contentHeight - visibleHeight;
    const thumbTop =
      maxScrollTop > 0
        ? (viewport.scrollTop / maxScrollTop) * maxThumbTop
        : 0;
    scrollbarThumb.style.height = `${thumbHeight}px`;
    scrollbarThumb.style.top = `${thumbTop}px`;
  }

  function hidePanel() {
    panel.style.display = "none";
    keyboardIndex = -1;
    mouseIndex = -1;
    currentResults = [];
    lastQuery = "";
    lastRenderedRequestId = -1;
    lastRenderedQuery = "";
    requestId++;
  }

  function showNotice(message) {
    currentResults = [];
    viewport.replaceChildren();
    const row = document.createElement("div");
    row.className = "amqRussianNoticeRow";
    row.textContent = message;
    viewport.appendChild(row);
    positionPanel();
    panel.style.display = "block";
    updateScrollbar();
  }

  function appendHighlightedText(container, text, query) {
    const source = String(text || "");
    const matcher = new RegExp(buildFlexibleTitlePattern(query), "giu");
    let previousIndex = 0;
    let matchResult;
    if (!matcher.test(source)) {
      container.textContent = source;
      return;
    }
    matcher.lastIndex = 0;
    while ((matchResult = matcher.exec(source))) {
      if (matchResult.index > previousIndex) {
        container.append(
          document.createTextNode(source.slice(previousIndex, matchResult.index))
        );
      }
      const match = document.createElement("span");
      match.className = "amqRussianMatch";
      match.textContent = matchResult[0];
      container.append(match);
      previousIndex = matcher.lastIndex;
      if (matchResult[0].length === 0) matcher.lastIndex++;
    }
    if (previousIndex < source.length) {
      container.append(document.createTextNode(source.slice(previousIndex)));
    }
  }

  function styleButton(button, state) {
    const matches = button.querySelectorAll(".amqRussianMatch");
    let foreground;
    if (state === "mouse") {
      button.style.backgroundColor = COLORS.current.accentColor;
      foreground = COLORS.current.panelBackground;
      button.style.color = foreground;
    } else if (state === "keyboard") {
      button.style.backgroundColor =
        `color-mix(in srgb, ${COLORS.current.accentColor} 80%, black)`;
      foreground = COLORS.current.textColor;
      button.style.color = foreground;
    } else {
      button.style.backgroundColor = COLORS.current.panelBackground;
      foreground = COLORS.current.textColor;
      button.style.color = foreground;
    }
    matches.forEach(match => {
      match.style.color =
        state ? foreground : COLORS.current.accentColor;
    });
  }

  function refreshButtonStates() {
    const buttons = [...viewport.querySelectorAll("button[data-result-index]")];
    buttons.forEach((button, index) => {
      let state = "";
      if (index === mouseIndex) {
        state = "mouse";
      } else if (index === keyboardIndex) {
        state = "keyboard";
      }
      styleButton(button, state);
      button.setAttribute(
        "aria-selected",
        String(index === keyboardIndex || index === mouseIndex)
      );
    });
  }

  function setKeyboardIndex(index) {
    const buttons = [...viewport.querySelectorAll("button[data-result-index]")];
    if (!buttons.length) return;
    keyboardIndex = (index + buttons.length) % buttons.length;
    refreshButtonStates();
    const selected = buttons[keyboardIndex];
    const rowTop = selected.offsetTop;
    const rowBottom = rowTop + selected.offsetHeight;
    const visibleTop = viewport.scrollTop;
    const visibleBottom = visibleTop + viewport.clientHeight;
    if (rowTop < visibleTop) {
      viewport.scrollTop = rowTop;
    } else if (rowBottom > visibleBottom) {
      viewport.scrollTop = rowBottom - viewport.clientHeight;
    }
  }

  function submitSelectedTitleAndSkip(result) {
    const input = getInput();
    const answerInput = unsafeWindow.quiz?.answerInput;
    if (!input || typeof answerInput?.submitAnswer !== "function") {
      console.error(
        "[AMQ Russian Dropdown] AMQ answer submission is unavailable; selected title was not submitted."
      );
      return;
    }
    hidePanel();
    const selectionId = ++selectionGeneration;
    const selectionRound = answerRound;
    input.value = result.amqValue;
    input.focus();
    setTimeout(() => {
      if (
        selectionId !== selectionGeneration ||
        selectionRound !== answerRound ||
        input.value !== result.amqValue
      ) {
        return;
      }
      try {
        answerInput.submitAnswer(true);
      } catch (error) {
        console.error(
          "[AMQ Russian Dropdown] AMQ could not submit the selected title and skip.",
          error
        );
      }
    }, 0);
  }

  function showResults(results, query) {
    const isSameResults = results.length === currentResults.length && results.every((r, i) => r.amqValue === currentResults[i].amqValue);
    if (isSameResults && lastRenderedQuery === query && panel.style.display !== "none") {
      return;
    }

    const selectedAmqTitle =
      keyboardIndex >= 0
        ? normalizeAmqTitle(currentResults[keyboardIndex]?.amqValue)
        : "";
    currentResults = results;
    keyboardIndex = selectedAmqTitle
      ? results.findIndex(
          result => normalizeAmqTitle(result.amqValue) === selectedAmqTitle
        )
      : -1;
    mouseIndex = -1;
    viewport.replaceChildren();
    if (!results.length) {
      panel.style.display = "none";
      return;
    }
    results.forEach((result, index) => {
      const button = document.createElement("button");
      button.type = "button";
      button.className = "amqRussianResultButton";
      button.dataset.resultIndex = String(index);
      button.setAttribute("aria-selected", "false");
      const russianTitle = document.createElement("span");
      appendHighlightedText(russianTitle, result.russian, query);
      const separator = document.createElement("span");
      separator.className = "amqRussianResultSeparator";
      separator.textContent = " / ";
      const amqTitle = document.createElement("span");
      amqTitle.className = "amqRussianResultAmqTitle";
      amqTitle.textContent = result.amqTitle;
      button.append(russianTitle, separator, amqTitle);
      button.addEventListener("pointerenter", () => {
        mouseIndex = index;
        refreshButtonStates();
      });
      button.addEventListener("pointerleave", () => {
        if (mouseIndex === index) {
          mouseIndex = -1;
          refreshButtonStates();
        }
      });
      button.addEventListener("pointerdown", event => {
        event.preventDefault();
      });
      button.addEventListener("click", () => {
        submitSelectedTitleAndSkip(result);
      });
      viewport.appendChild(button);
    });
    positionPanel();
    panel.style.display = "block";
    updateScrollbar();
    refreshButtonStates();
    lastRenderedQuery = query;
  }

  function renderSearchResults(animes, query, currentRequest, titleIndex) {
    if (!Array.isArray(animes)) return;

    const isCurrent = currentRequest === requestId;
    const isStaleRelevant =
      !isCurrent &&
      query.length > 0 &&
      lastQuery.length > query.length &&
      lastQuery.startsWith(query);
    if (!isCurrent && !isStaleRelevant) return;

    if (currentRequest < lastRenderedRequestId) return;

    const targetQuery = isCurrent ? query : lastQuery;

    const bestResultByAmqTitle = new Map();
    const normalizedQuery = normalize(targetQuery);
    for (const anime of animes) {
      if (!anime?.russian || !anime?.name) continue;

      if (anime.malId && !nameItemRussianTitleCache.has(`mal:${anime.malId}`)) {
        const aliases = Array.isArray(anime.russianAliases) ? anime.russianAliases : [];
        if (anime.russian || aliases.length > 0) {
          nameItemRussianTitleCache.set(`mal:${anime.malId}`, Promise.resolve({
            animeRussian: anime.russian?.trim() || null,
            russianAliases: aliases.map(a => a.trim()).filter(Boolean)
          }));
        }
      }

      const namesToCheck = [
        anime.russian,
        ...(Array.isArray(anime.russianAliases) ? anime.russianAliases : []),
        ...(Array.isArray(anime.synonyms) ? anime.synonyms : [])
      ];

      const matchedName = namesToCheck.find(name => typeof name === "string" && findTitleMatches(name, targetQuery));
      if (!matchedName) continue;

      const exactStringMatch = typeof anime.name === 'string' ? getAmqExactStringIndex()?.get(anime.name.toLowerCase()) : null;
      const match =
        getAmqTitleMatchForAnime(anime) ||
        exactStringMatch ||
        getExactAmqTitleIndex()?.get(normalizeAmqTitle(anime.name)) ||
        titleIndex.get(normalize(anime.name)) ||
        { value: anime.name, label: anime.name };

      const result = {
        id: anime.id,
        malId: Number(anime.malId) || null,
        russian: matchedName,
        amqTitle: anime.preferredTitle || anime.name || match.label,
        amqValue: match.value,
        titlePriority: Number(anime.titlePriority) || 0,
        relevance: getSearchResultRelevance(matchedName, normalizedQuery)
      };
      const key = normalizeAmqTitle(match.value);
      const current = bestResultByAmqTitle.get(key);
      if (
        !current ||
        result.titlePriority > current.titlePriority ||
        (
          result.titlePriority === current.titlePriority &&
          result.relevance > current.relevance
        )
      ) {
        bestResultByAmqTitle.set(key, result);
      }
    }
    const results = [...bestResultByAmqTitle.values()];
    results.sort(
      (a, b) =>
        b.titlePriority - a.titlePriority ||
        b.relevance - a.relevance ||
        a.russian.localeCompare(b.russian, "ru")
    );
    if (results.length) {
      showResults(results, targetQuery);
      lastRenderedRequestId = currentRequest;
    } else if (!currentResults.length) {
      panel.style.display = "none";
    }
  }

  function getSearchResultRelevance(title, normalizedQuery) {
    const normalizedTitle = normalize(title);
    let score = 0;
    if (normalizedTitle === normalizedQuery) score += 1000;
    else if (normalizedTitle.startsWith(normalizedQuery)) score += 500;
    else if (normalizedTitle.includes(` ${normalizedQuery}`)) score += 200;

    if (/\b(?:ova|oav|special|recap|movie|film)\b/i.test(title)) {
      score -= 1000;
    }
    return score - normalizedTitle.length;
  }

  function search(query, currentRequest) {
    const titleIndex = getAmqTitleIndex();
    if (!titleIndex?.size) {
      showNotice("Список названий AMQ пока недоступен.");
      return;
    }
    const accumulatedResults = new Map();
    const addResults = animes => {
      if (!Array.isArray(animes) || !animes.length) return;
      for (const anime of animes) {
        if (!anime?.russian || !anime?.name) continue;
        const key = anime.malId
          ? `mal:${anime.malId}`
          : `${normalizeAmqTitle(anime.russian)}\u0000${normalizeAmqTitle(anime.name)}`;
        const current = accumulatedResults.get(key);
        if (!current || (!current.preferredTitle && anime.preferredTitle)) {
          accumulatedResults.set(key, anime);
        }
      }
      renderSearchResults(
        [...accumulatedResults.values()],
        query,
        currentRequest,
        titleIndex
      );
    };
    requestSearchCandidates(query, databaseResults => {
      addResults(databaseResults);
    })
      .then(animes => {
        addResults(animes);
      })
      .catch(error => {
        if (
          currentRequest === requestId &&
          accumulatedResults.size === 0 &&
          currentResults.length === 0
        ) {
          showNotice(`Ошибка поиска: ${error.message}`);
        }
      });
  }

  document.addEventListener(
    "wheel",
    event => {
      if (panel.style.display === "none" || !panel.contains(event.target)) {
        return;
      }
      event.preventDefault();
      event.stopImmediatePropagation();
      viewport.scrollTop += event.deltaY;
      updateScrollbar();
    },
    { capture: true, passive: false }
  );

  scrollbarThumb.addEventListener("pointerdown", event => {
    event.preventDefault();
    dragStartY = event.clientY;
    dragStartScrollTop = viewport.scrollTop;
    scrollbarThumb.classList.add("is-dragging");
    scrollbarThumb.setPointerCapture(event.pointerId);
  });

  scrollbarThumb.addEventListener("pointermove", event => {
    if (!scrollbarThumb.hasPointerCapture(event.pointerId)) return;
    const maxThumbTop =
      scrollbarTrack.clientHeight - scrollbarThumb.offsetHeight;
    const maxScrollTop = viewport.scrollHeight - viewport.clientHeight;
    if (maxThumbTop <= 0 || maxScrollTop <= 0) return;
    const delta = event.clientY - dragStartY;
    const newThumbTop = Math.max(
      0,
      Math.min(
        maxThumbTop,
        (dragStartScrollTop / maxScrollTop) * maxThumbTop + delta
      )
    );
    viewport.scrollTop = (newThumbTop / maxThumbTop) * maxScrollTop;
  });

  function stopDragging(event) {
    if (scrollbarThumb.hasPointerCapture(event.pointerId)) {
      scrollbarThumb.releasePointerCapture(event.pointerId);
    }
    scrollbarThumb.classList.remove("is-dragging");
  }

  scrollbarThumb.addEventListener("pointerup", stopDragging);
  scrollbarThumb.addEventListener("pointercancel", stopDragging);
  viewport.addEventListener("scroll", updateScrollbar);

  document.addEventListener(
    "keydown",
    event => {
      if (!event.target.matches("#qpAnswerInput")) return;
      if (panel.style.display === "none") return;
      const buttons = viewport.querySelectorAll("button[data-result-index]");
      if (!buttons.length) return;
      if (event.key === "ArrowDown") {
        event.preventDefault();
        event.stopImmediatePropagation();
        setKeyboardIndex(keyboardIndex < 0 ? 0 : keyboardIndex + 1);
      } else if (event.key === "ArrowUp") {
        event.preventDefault();
        event.stopImmediatePropagation();
        setKeyboardIndex(keyboardIndex < 0 ? 0 : keyboardIndex - 1);
      } else if (event.key === "Enter") {
        event.preventDefault();
        event.stopImmediatePropagation();
        if (event.repeat) return;
        const selectedIndex = keyboardIndex >= 0 ? keyboardIndex : 0;
        const result = currentResults[selectedIndex];
        if (result) submitSelectedTitleAndSkip(result);
      }
    },
    true
  );

  document.addEventListener("input", event => {
    if (!event.target.matches("#qpAnswerInput")) return;
    clearTimeout(debounceTimer);
    const query = event.target.value.trim();

    const isRelated =
      query.length > 0 &&
      lastQuery.length > 0 &&
      (query.startsWith(lastQuery) || lastQuery.startsWith(query));

    if (!isRelated) {
      hidePanel();
    } else if (currentResults.length > 0) {
      const matchingResults = currentResults.filter(r =>
        findTitleMatches(r.russian, query)
      );

      if (matchingResults.length > 0) {
        showResults(matchingResults, query);
      } else {
        panel.style.display = "none";
        keyboardIndex = -1;
        mouseIndex = -1;
      }
    }

    lastQuery = query;
    const currentRequest = ++requestId;

    if (query.length < 2 || !/[а-яё]/i.test(query)) return;
    debounceTimer = setTimeout(() => {
      search(query, currentRequest);
    }, SEARCH_DEBOUNCE_MS);
  });

  document.addEventListener("pointerdown", event => {
    if (
      !panel.contains(event.target) &&
      !event.target.matches("#qpAnswerInput")
    ) {
      hidePanel();
    }
  });

  window.addEventListener("resize", positionPanel);
  window.addEventListener("scroll", positionPanel, true);

  let listenerAttempts = 0;
  const answerTitleListenerInterval = setInterval(() => {
    listenerAttempts++;
    if (listenerAttempts > MAX_LISTENER_ATTEMPTS) {
      console.warn(
        "[AMQ Russian Dropdown] Listener setup timed out; some features may be unavailable."
      );
      clearInterval(answerTitleListenerInterval);
      return;
    }
    if (typeof Listener !== "function") return;
    if (!document.querySelector("#loadingScreen.hidden")) return;
    const listenerReady = setupAnswerRussianTitleListener();
    const multipleChoiceReady = setupMultipleChoiceTitleTranslation();
    updateSongHistoryRussianTitles();
    if (listenerReady && multipleChoiceReady) {
      clearInterval(answerTitleListenerInterval);
    }
  }, 500);

  let songHistoryUpdateFrame = 0;
  const songHistoryObserver = new MutationObserver(records => {
    const isGeneratedNode = node =>
      node.nodeType === Node.ELEMENT_NODE &&
      (
        node.matches("#shiAnimeRussianTitle, [data-amq-russian-alias], [data-amq-russian-title]") ||
        node.querySelector("#shiAnimeRussianTitle, [data-amq-russian-alias], [data-amq-russian-title]")
      );

    const isRelevantChange = records.some(record => {
      if (record.target.nodeType === Node.ELEMENT_NODE &&
          (record.target.matches("#shiAnimeRussianTitle, [data-amq-russian-alias], [data-amq-russian-title]") ||
           record.target.closest("#shiAnimeRussianTitle, [data-amq-russian-alias], [data-amq-russian-title]"))) {
        return false;
      }
      if (record.type === "attributes" && record.attributeName === "href") {
        return true;
      }
      return [...record.addedNodes].some(node => !isGeneratedNode(node));
    });

    if (!isRelevantChange || songHistoryUpdateFrame) return;
    songHistoryUpdateFrame = requestAnimationFrame(() => {
      songHistoryUpdateFrame = 0;
      updateSongHistoryRussianTitles();
    });
  });

  songHistoryObserver.observe(document.body, {
    childList: true,
    subtree: true,
    characterData: true,
    attributes: true,
    attributeFilter: ["href"]
  });

  const SCRIPT_CSS = `
    #amqRussianTitlePanel { display: none; position: absolute; z-index: 999999; border: 0; border-radius: 8px; box-shadow: 0 0 10px 2px #000; overflow: hidden; font-weight: 400; }
    .amqRussianPositioned { position: relative; }
    #amqRussianListViewport { position: relative; max-height: 260px; overflow-y: auto; overflow-x: hidden; overscroll-behavior: contain; scrollbar-width: none; -ms-overflow-style: none; }
    #amqRussianListViewport::-webkit-scrollbar { display: none; width: 0; height: 0; }
    #amqRussianScrollbarTrack { position: absolute; z-index: 3; top: 0; right: 0; bottom: 0; width: 8px; background: transparent; pointer-events: none; }
    #amqRussianScrollbarThumb { position: absolute; top: 0; right: 1px; width: 6px; min-height: 20px; background: rgba(255, 255, 255, 0.4); border-radius: 5px; pointer-events: auto; cursor: pointer; transform: scaleX(1); transform-origin: right center; transition: transform 120ms ease, background-color 120ms ease; }
    #amqRussianScrollbarThumb:hover, #amqRussianScrollbarThumb.is-dragging { background: color-mix(in srgb, var(--amq-russian-accent) 40%, transparent); transform: scaleX(1.5); }
    .amqAnswerRussianTitle { position: absolute; left: -253px; top: 50%; transform: translateY(-50%); box-sizing: border-box; width: 243px; min-height: 79px; padding: 12px 10px; display: none; align-items: center; justify-content: center; border-radius: 6px; background: var(--primaryColor, var(--primarycolor, rgba(0, 0, 0, .9))); color: #f0f0f0; font-size: 15px; font-weight: 400; line-height: 1.35; text-align: center; white-space: normal; overflow-wrap: anywhere; z-index: 1000; box-shadow: 0 2px 8px rgba(0, 0, 0, .25); }
    .amqAnswerRussianTitleText { max-height: calc(100vh - 40px); overflow-y: auto; scrollbar-width: none; -ms-overflow-style: none; }
    .amqAnswerRussianTitleText::-webkit-scrollbar { display: none; width: 0; height: 0; }
    .amqAnswerRussianTitleArrow { position: absolute; right: -10px; top: 50%; transform: translateY(-50%); width: 0; height: 0; border-top: 11px solid transparent; border-bottom: 11px solid transparent; border-left: 10px solid var(--primaryColor, var(--primarycolor, rgba(0, 0, 0, .9))); }
    .amqRussianNoticeRow { padding: 9px; text-align: center; font-weight: 400; white-space: normal; }
    .amqRussianResultButton { display: block; width: 100%; min-height: 6px; padding: 6px 12px; text-align: center; border: 0; cursor: pointer; font: inherit; font-weight: 400; line-height: 1.35; }
    .amqRussianResultSeparator, .amqRussianResultAmqTitle { opacity: .5; }
    .amqRussianMatch { color: var(--amq-russian-accent); font-weight: 400; }
  `;

  const scriptStyle = document.createElement("style");
  scriptStyle.textContent = SCRIPT_CSS;
  document.head.appendChild(scriptStyle);

})();
