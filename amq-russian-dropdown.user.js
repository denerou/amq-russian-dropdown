// ==UserScript==
// @name         AMQ Russian dropdown
// @version      2.1.2
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
  const SHIKIMORI_CACHE_TTL_MS = 24 * 60 * 60 * 1000;
  const shikimoriTitleCache = new Map();
  const pendingShikimoriLookups = new Map();
  const shikimoriSearchCache = new Map();
  const pendingShikimoriSearches = new Map();
  const SHIKIMORI_SEARCH_CACHE_TTL_MS = 10 * 60 * 1000;
  const confirmedDiscoveredMalIds = new Set();
  const SEARCH_INDICATOR_TIMEOUT_MS = 2500;
  const TITLE_TRANSLITERATION_GROUPS = [
    ["си", "ши"], ["ти", "чи"], ["цу", "тсу"], ["дзи", "джи"], ["фу", "ху"],
    ["ся", "ша"], ["сю", "шу"], ["сё", "шо"], ["тя", "ча"], ["тю", "чу"],
    ["тё", "чо"], ["дзя", "джа"], ["дзю", "джу"], ["дзё", "джё"],
    ["мба", "нба"], ["мпа", "нпа"], ["мма", "нма"],
    ["нъа", "н-а"], ["нъи", "н-и"], ["нъя", "нья"], ["тти", "ччи"],
    ["й", "и"], ["йо", "ио", "ё"], ["дз", "з"], ["ё", "е"], ["cё", "шо"], ["е", "э"]
  ].sort((left, right) => right[0].length - left[0].length);

  // Кэши и состояние поиска
  let amqTitlesCache = null;
  let amqTitleIndexCache = null;
  let exactAmqTitleIndexCache = null;

  // Нормализация названий и подготовка поиска

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
    for (const group of TITLE_TRANSLITERATION_GROUPS) {
      const matched = group.find(value =>
        characters.slice(index, index + value.length).join("") === value
      );
      if (matched) return { length: matched.length, alternatives: group };
    }

    const character = characters[index];
    if (character !== "е" && character !== "э") return null;

    const previous = characters[index - 1] || "";
    if (/[аеёиоуыэюя]/u.test(previous)) {
      return {
        length: 1,
        alternatives: [character, character === "е" ? "э" : "е"]
      };
    }

    if (/[\p{L}]/u.test(previous) || index === 0 || !/[\p{L}\p{N}]/u.test(previous)) {
      return { length: 1, alternatives: [character, character === "е" ? "э" : "е"] };
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

  function findTitleMatches(title, query) {
    return new RegExp(buildFlexibleTitlePattern(query), "iu").test(title);
  }

  // Поисковые варианты по правилам русской передачи японских слогов

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

  // Объединение результатов и сопоставление с AMQ

  function mergeAnimeResults(responses) {
    const animes = new Map();
    for (const response of responses) {
      if (!Array.isArray(response)) continue;
      for (const anime of response) {
        if (!anime?.russian || !anime?.name) continue;
        const key =
          `${normalizeAmqTitle(anime.russian)}\u0000${normalizeAmqTitle(anime.name)}`;
        if (!animes.has(key)) animes.set(key, anime);
      }
    }
    return [...animes.values()];
  }

  function hasUsableSearchMatch(animes, query) {
    return animes.some(anime =>
      anime?.russian &&
      anime?.name &&
      findTitleMatches(anime.russian, query) &&
      getAmqTitleMatchForAnime(anime)
    );
  }

  function getAmqTitleMatchForAnime(anime) {
    const exactTitleIndex = getExactAmqTitleIndex();
    const names = [
      anime?.name,
      ...(Array.isArray(anime?.english) ? anime.english : []),
      ...(Array.isArray(anime?.japanese) ? anime.japanese : []),
      ...(Array.isArray(anime?.synonyms) ? anime.synonyms : [])
    ];
    for (const name of names) {
      if (typeof name !== "string") continue;
      const exactMatch = exactTitleIndex?.get(normalizeAmqTitle(name));
      if (exactMatch) return exactMatch;
    }
    return null;
  }

  // Поиск тайтлов на Shikimori

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
          if (
            Number.isSafeInteger(anime?.id) &&
            typeof anime?.russian === "string" &&
            findTitleMatches(anime.russian, query)
          ) {
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
      const detailCandidates = [...candidates.values()].slice(0, 12);
      const detailResponses = [];
      for (let index = 0; index < detailCandidates.length; index += 4) {
        detailResponses.push(
          ...await Promise.allSettled(
            detailCandidates.slice(index, index + 4).map(candidate =>
              requestJsonWithRetry(
                `https://${SHIKIMORI_API_HOST}/api/animes/${candidate.id}`,
                undefined
              )
            )
          )
        )
      }
      for (const response of detailResponses) {
        if (response.status === "rejected") {
          lastError = response.reason;
          continue;
        }
        const anime = extractShikimoriAnime(response.value);
        if (
          !anime ||
          typeof anime.russian !== "string" ||
          !findTitleMatches(anime.russian, query)
        ) {
          continue;
        }
        const amqTitle = getAmqTitleMatchForAnime(anime);
        const malId = Number(anime.myanimelist_id);
        if (!amqTitle || !Number.isSafeInteger(malId) || malId < 1) continue;
        results.push({
          id: malId,
          malId,
          name: amqTitle.value,
          amqTitle: amqTitle.label,
          russian: anime.russian.trim()
        });
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

  // Проверка и сохранение найденных тайтлов через API

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
        } catch {}
      }
    })();
  }

  // Поиск в базе и объединение результатов с Shikimori

  async function requestSearchCandidates(
    query,
    onDatabaseResults
  ) {
    const requestCandidate = candidate =>
      requestJson(`${API_BASE}/api/search?q=${encodeURIComponent(candidate)}`);
    let databaseResults = [];
    let shikimoriResults = [];
    const publishResults = () => {
      const results = mergeAnimeResults([databaseResults, shikimoriResults]);
      if (
        results.some(anime =>
          anime?.russian &&
          anime?.name &&
          findTitleMatches(anime.russian, query)
        )
      ) {
        onDatabaseResults(results);
      }
    };
    const shikimoriSearch = requestShikimoriSearchCandidates(query).then(
      results => {
        shikimoriResults = results;
        publishResults();
        return { results };
      },
      error => ({ error })
    );
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

    const fallbackQueries = hasUsableSearchMatch(mergedDirectResults, query)
      ? []
      : getCandidateSearchQueries(query)
          .filter(candidate => candidate !== query.trim());
    const fallbackSearch = Promise.allSettled(
      fallbackQueries.map(requestCandidate)
    );
    const responses = await fallbackSearch;
    const successfulResponses = responses
      .filter(response => response.status === "fulfilled")
      .map(response => response.value);
    databaseResults = mergeAnimeResults([
      directResults,
      ...successfulResponses
    ]);
    publishResults();
    const shikimoriResponse = await shikimoriSearch;
    if (
      shikimoriResponse.error &&
      !hasUsableSearchMatch(databaseResults, query)
    ) {
      throw directError || shikimoriResponse.error;
    }
    shikimoriResults = shikimoriResponse.results || [];
    if (
      directError &&
      successfulResponses.length === 0 &&
      shikimoriResults.length === 0
    ) {
      throw directError;
    }
    const databaseRussianTitles = new Set(
      databaseResults.map(anime => normalizeAmqTitle(anime.russian))
    );
    shikimoriResults = shikimoriResults.filter(
      anime => !databaseRussianTitles.has(normalizeAmqTitle(anime.russian))
    );
    persistDiscoveredShikimoriTitles(
      shikimoriResults,
      query,
      databaseResults
    );
    return mergeAnimeResults([databaseResults, shikimoriResults]);
  }

  // Получение и индексация списка названий AMQ

  function getAmqTitles() {
    if (amqTitlesCache) return amqTitlesCache;
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

  // HTTP-запросы, повторы и проверка ответов

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
        timeout: 15000,
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

  async function requestJsonWithRetry(url, options, maxAttempts = 3) {
    for (let attempt = 1; ; attempt++) {
      try {
        return await requestJson(url, options);
      } catch (error) {
        const retryable =
          error.statusCode === 429 ||
          (error.statusCode >= 500 && error.statusCode <= 599);
        if (!retryable || attempt >= maxAttempts) throw error;
        await new Promise(resolve =>
          setTimeout(resolve, 1000 * 2 ** (attempt - 1))
        );
      }
    }
  }

  function extractShikimoriAnime(response) {
    return Array.isArray(response) ? response[0] : response;
  }

  function getVerifiedRussianTitle(anime, malId, requireApiSource = false) {
    if (
      Number(anime?.myanimelist_id ?? anime?.malId) !== malId ||
      typeof anime?.russian !== "string" ||
      (requireApiSource && anime?.source !== SHIKIMORI_API_HOST)
    ) {
      return "";
    }
    return anime.russian.trim();
  }

  async function requestShikimoriTitle(malId) {
    const directUrl = `https://${SHIKIMORI_API_HOST}/api/animes/${malId}`;
    try {
      const anime = extractShikimoriAnime(await requestJson(directUrl));
      const title = getVerifiedRussianTitle(anime, malId);
      if (title) return title;
    } catch (error) {
    }
    const searchUrl = new URL(`https://${SHIKIMORI_API_HOST}/api/animes`);
    searchUrl.searchParams.set("myanimelist_id", String(malId));
    searchUrl.searchParams.set("limit", "10");
    const candidatesResponse = await requestJson(searchUrl.href);
    const candidates = Array.isArray(candidatesResponse)
      ? candidatesResponse
      : [];
    const matchingCandidates = candidates.filter(
      candidate => Number(candidate?.myanimelist_id) === malId
    );
    const candidateDetails = matchingCandidates.length
      ? matchingCandidates
      : candidates.filter(candidate => Number.isSafeInteger(candidate?.id));
    const details = await Promise.all(
      candidateDetails.slice(0, 10).map(async candidate => {
        if (Number(candidate?.myanimelist_id) === malId) return candidate;
        return extractShikimoriAnime(
          await requestJson(
            `https://${SHIKIMORI_API_HOST}/api/animes/${candidate.id}`
          )
        );
      })
    );
    const title = details
      .map(anime => getVerifiedRussianTitle(anime, malId))
      .find(Boolean);
    if (!title) {
      throw new Error(`Shikimori.io has no verified anime for MAL ID ${malId}`);
    }
    return title;
  }

  function requestShikimoriRussianTitle(malId) {
    const cached = shikimoriTitleCache.get(malId);
    if (cached && cached.expiresAt > Date.now()) {
      return Promise.resolve(cached.title);
    }
    if (pendingShikimoriLookups.has(malId)) {
      return pendingShikimoriLookups.get(malId);
    }
    const lookup = (async () => {
      try {
        return await requestShikimoriTitle(malId);
      } catch (error) {
      }
      const apiUrl =
        `${API_BASE}/api/shikimori/anime?malId=${encodeURIComponent(malId)}`;
      const anime = extractShikimoriAnime(await requestJson(apiUrl));
      const title = getVerifiedRussianTitle(anime, malId, true);
      if (!title) {
        throw new Error(
          `Could not get a verified Russian title for MAL ID ${malId} from Shikimori.io or the VPS API`
        );
      }
      return title;
    })().then(title => {
      shikimoriTitleCache.set(malId, {
        title,
        expiresAt: Date.now() + SHIKIMORI_CACHE_TTL_MS
      });
      return title;
    });
    pendingShikimoriLookups.set(malId, lookup);
    return lookup.finally(() => pendingShikimoriLookups.delete(malId));
  }

  // Визуальная часть: элементы интерфейса и их состояние

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

  let activeShikimoriRequest = 0;

  let debounceTimer;
  let statusTimer;
  let searchIndicatorTimer;
  let requestId = 0;
  let keyboardIndex = -1;
  let mouseIndex = -1;
  let currentResults = [];
  let dragStartY = 0;
  let dragStartScrollTop = 0;
  let answerRound = 0;
  let selectionGeneration = 0;
  let pendingNativeSelection = null;
  let applyingNativeSelection = false;

  // Подсказка с русским названием после ответа

  function setShikimoriTooltipText(tooltip, text) {
    const content = tooltip.querySelector(".amqShikimoriRussianTitleText");
    if (content) content.textContent = text;
  }

  function ensureShikimoriTooltip(container) {
    const tooltipClass = "amqShikimoriRussianTitle";
    let tooltip = container.querySelector(`.${tooltipClass}`);
    if (tooltip) return tooltip;
    tooltip = document.createElement("div");
    tooltip.className = tooltipClass;
    tooltip.setAttribute("role", "status");
    const content = document.createElement("span");
    content.className = "amqShikimoriRussianTitleText";
    const arrow = document.createElement("div");
    arrow.className = "amqShikimoriRussianTitleArrow";
    arrow.setAttribute("aria-hidden", "true");
    tooltip.append(content, arrow);
    if (getComputedStyle(container).position === "static") {
      container.classList.add("amqRussianPositioned");
    }
    container.appendChild(tooltip);
    container.addEventListener("mouseenter", () => {
      if (content.textContent.trim()) tooltip.style.display = "flex";
    });
    container.addEventListener("mouseleave", () => {
      tooltip.style.display = "none";
    });
    return tooltip;
  }

  function handleAnswerResults(data) {
    answerRound++;
    cancelPendingNativeSelection("new answer round");
    keyboardIndex = -1;
    mouseIndex = -1;
    currentResults = [];
    hidePanel();
    const currentRequest = ++activeShikimoriRequest;
    const malId = Number(data?.songInfo?.siteIds?.malId);
    const container = document.querySelector("#qpAnimeNameContainer");
    if (!container || !Number.isSafeInteger(malId) || malId < 1) return;
    const tooltip = ensureShikimoriTooltip(container);
    setShikimoriTooltipText(tooltip, "Загружаю русское название…");
    tooltip.style.display = "none";
    requestShikimoriRussianTitle(malId)
      .then(title => {
        if (currentRequest !== activeShikimoriRequest || !container.isConnected) {
          return;
        }
        setShikimoriTooltipText(tooltip, title);
        if (container.matches(":hover")) tooltip.style.display = "flex";
      })
      .catch(error => {
        if (currentRequest !== activeShikimoriRequest) return;
        setShikimoriTooltipText(tooltip, `Ошибка: ${error.message}`);
        if (container.matches(":hover")) tooltip.style.display = "flex";
      });
  }

  function setupShikimoriTitleListener() {
    if (typeof Listener !== "function") {
      return;
    }
    new Listener("answer results", handleAnswerResults).bindListener();
  }

  // Dropdown: оформление, отображение и взаимодействие

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

  function stopStatusAnimation() {
    if (statusTimer) {
      clearInterval(statusTimer);
      statusTimer = undefined;
    }
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
    stopStatusAnimation();
    clearTimeout(searchIndicatorTimer);
    panel.style.display = "none";
    keyboardIndex = -1;
    mouseIndex = -1;
    requestId++;
  }

  function showSearching() {
    stopStatusAnimation();
    currentResults = [];
    viewport.replaceChildren();
    const row = document.createElement("div");
    row.className = "amqRussianStatusRow";
    viewport.appendChild(row);
    const frames = ["...", ".", ".."];
    let frameIndex = 0;
    row.textContent = frames[frameIndex];
    statusTimer = setInterval(() => {
      frameIndex = (frameIndex + 1) % frames.length;
      row.textContent = frames[frameIndex];
    }, 200);
    positionPanel();
    panel.style.display = "block";
    updateScrollbar();
  }

  function showNotice(message) {
    stopStatusAnimation();
    clearTimeout(searchIndicatorTimer);
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

  function cancelPendingNativeSelection(reason) {
    if (!pendingNativeSelection) return;
    clearTimeout(pendingNativeSelection.timer);
    console.debug("[AMQ Russian Dropdown] Cancelled pending selection", {
      reason,
      answer: pendingNativeSelection.answer,
      selectionRound: pendingNativeSelection.round,
      currentRound: answerRound
    });
    pendingNativeSelection = null;
    selectionGeneration++;
  }

  function refreshNativeAutocomplete() {
    const controller =
      unsafeWindow.quiz?.answerInput?.typingInput?.autoCompleteController;
    if (typeof controller?.newList !== "function") {
      console.error(
        "[AMQ Russian Dropdown] AMQ autocomplete controller is unavailable; " +
        "selection was cancelled without dispatching a synthetic input event."
      );
      return false;
    }
    try {
      controller.newList();
      return true;
    } catch (error) {
      console.error(
        "[AMQ Russian Dropdown] Failed to refresh AMQ autocomplete.",
        error
      );
      return false;
    }
  }

  function submitNativeAnswer(answer) {
    const typingInput = unsafeWindow.quiz?.answerInput?.typingInput;
    if (!typingInput) {
      throw new Error("AMQ answer input is not available");
    }
    const submitAnswer =
      Object.getPrototypeOf(Object.getPrototypeOf(typingInput))?.submitAnswer;
    if (typeof submitAnswer !== "function") {
      throw new Error("AMQ submitAnswer method is not available");
    }
    submitAnswer.call(typingInput, answer);
  }

  function chooseNativeAmqOption(result, submitAfterSelection) {
    const input = getInput();
    if (!input) return;
    cancelPendingNativeSelection("superseded by a new selection");
    hidePanel();
    const selectionId = ++selectionGeneration;
    const selectionRound = answerRound;
    pendingNativeSelection = {
      answer: result.amqValue,
      round: selectionRound,
      timer: null
    };
    input.value = result.amqValue;
    input.focus();
    if (!refreshNativeAutocomplete()) {
      cancelPendingNativeSelection("autocomplete refresh failed");
      return;
    }
    let attempts = 0;
    function selectAmqOption() {
      if (
        !pendingNativeSelection ||
        selectionId !== selectionGeneration ||
        selectionRound !== answerRound ||
        input.value !== result.amqValue
      ) {
        cancelPendingNativeSelection("selection became stale");
        return;
      }
      const list = document.querySelector(
        "#qpAnswerInputContainer .awesomplete ul"
      );
      const options = list
        ? [...list.querySelectorAll("li[role='option'], li")]
        : [];
      const target = normalize(result.amqValue);
      const option = options.find(
        item => normalize(item.textContent) === target
      );
      if (option) {
        applyingNativeSelection = true;
        try {
          option.dispatchEvent(
            new MouseEvent("mousedown", {
              bubbles: true,
              cancelable: true,
              view: unsafeWindow
            })
          );
        } finally {
          applyingNativeSelection = false;
        }
        if (
          selectionRound === answerRound &&
          input.value === result.amqValue &&
          submitAfterSelection
        ) {
          submitNativeAnswer(result.amqValue);
        }
        pendingNativeSelection = null;
        return;
      }
      if (attempts++ < 20) {
        pendingNativeSelection.timer = setTimeout(selectAmqOption, 25);
      } else {
        console.warn(
          "[AMQ Russian Dropdown] Native AMQ suggestion did not appear in time.",
          { answer: result.amqValue, attempts, round: answerRound }
        );
        pendingNativeSelection = null;
      }
    }
    pendingNativeSelection.timer = setTimeout(selectAmqOption, 0);
  }

  function showResults(results, query) {
    stopStatusAnimation();
    clearTimeout(searchIndicatorTimer);
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
        chooseNativeAmqOption(result, false);
      });
      viewport.appendChild(button);
    });
    positionPanel();
    panel.style.display = "block";
    updateScrollbar();
    refreshButtonStates();
  }

  function renderSearchResults(animes, query, currentRequest, titleIndex) {
    if (currentRequest !== requestId || !Array.isArray(animes)) return;
    const bestResultByAmqTitle = new Map();
    const normalizedQuery = normalize(query);
    for (const anime of animes) {
      if (!anime?.russian || !anime?.name) continue;
      if (!findTitleMatches(anime.russian, query)) continue;
      const match =
        getExactAmqTitleIndex()?.get(normalizeAmqTitle(anime.name)) ||
        titleIndex.get(normalize(anime.name)) ||
        { value: anime.name, label: anime.name };
      const result = {
        id: anime.id,
        russian: anime.russian,
        amqTitle: match.label,
        amqValue: match.value,
        relevance: getSearchResultRelevance(anime.russian, normalizedQuery)
      };
      const key = normalizeAmqTitle(match.value);
      const current = bestResultByAmqTitle.get(key);
      if (!current || result.relevance > current.relevance) {
        bestResultByAmqTitle.set(key, result);
      }
    }
    const results = [...bestResultByAmqTitle.values()];
    results.sort(
      (a, b) =>
        b.relevance - a.relevance ||
        a.russian.localeCompare(b.russian, "ru")
    );
    if (results.length) {
      showResults(results, query);
    } else {
      stopStatusAnimation();
      clearTimeout(searchIndicatorTimer);
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
    showSearching();
    clearTimeout(searchIndicatorTimer);
    searchIndicatorTimer = setTimeout(() => {
      if (currentRequest !== requestId || currentResults.length) return;
      stopStatusAnimation();
      panel.style.display = "none";
    }, SEARCH_INDICATOR_TIMEOUT_MS);
    const accumulatedResults = new Map();
    const addResults = animes => {
      for (const anime of animes) {
        if (!anime?.russian || !anime?.name) continue;
        const key =
          `${normalizeAmqTitle(anime.russian)}\u0000${normalizeAmqTitle(anime.name)}`;
        if (!accumulatedResults.has(key)) accumulatedResults.set(key, anime);
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
        if (currentRequest === requestId) {
          showNotice(`Ошибка поиска: ${error.message}`);
        }
      });
  }



  // Обработчики событий страницы

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
      } else if (event.key === "Enter" && keyboardIndex >= 0) {
        event.preventDefault();
        event.stopImmediatePropagation();
        const result = currentResults[keyboardIndex];
        if (result) chooseNativeAmqOption(result, true);
      }
    },
    true
  );

  document.addEventListener("input", event => {
    if (!event.target.matches("#qpAnswerInput")) return;
    if (applyingNativeSelection) return;
    cancelPendingNativeSelection("answer input changed");
    clearTimeout(debounceTimer);
    const query = event.target.value.trim();
    const currentRequest = ++requestId;
    clearTimeout(searchIndicatorTimer);
    currentResults = [];
    keyboardIndex = -1;
    mouseIndex = -1;
    panel.style.display = "none";
    if (query.length < 2 || !/[а-яё]/i.test(query)) return;
    debounceTimer = setTimeout(() => {
      search(query, currentRequest);
    }, 200);
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

  const shikimoriListenerInterval = setInterval(() => {
    if (document.querySelector("#loadingScreen.hidden")) {
      clearInterval(shikimoriListenerInterval);
      setupShikimoriTitleListener();
    }
  }, 500);

  // CSS: стили dropdown, подсказок и уведомлений
  const SCRIPT_CSS = `
    #amqRussianTitlePanel { display: none; position: absolute; z-index: 999999; border: 0; border-radius: 8px; box-shadow: 0 0 10px 2px #000; overflow: hidden; font-weight: 400; }
    .amqRussianPositioned { position: relative; }
    #amqRussianListViewport { position: relative; max-height: 260px; overflow-y: auto; overflow-x: hidden; overscroll-behavior: contain; scrollbar-width: none; -ms-overflow-style: none; }
    #amqRussianListViewport::-webkit-scrollbar { display: none; width: 0; height: 0; }
    #amqRussianScrollbarTrack { position: absolute; z-index: 3; top: 0; right: 0; bottom: 0; width: 8px; background: transparent; pointer-events: none; }
    #amqRussianScrollbarThumb { position: absolute; top: 0; right: 1px; width: 6px; min-height: 20px; background: rgba(255, 255, 255, 0.4); border-radius: 5px; pointer-events: auto; cursor: pointer; transform: scaleX(1); transform-origin: right center; transition: transform 120ms ease, background-color 120ms ease; }
    #amqRussianScrollbarThumb:hover, #amqRussianScrollbarThumb.is-dragging { background: color-mix(in srgb, var(--amq-russian-accent) 40%, transparent); transform: scaleX(1.5); }
    .amqShikimoriRussianTitle { position: absolute; left: -253px; top: 50%; transform: translateY(-50%); box-sizing: border-box; width: 243px; min-height: 79px; padding: 12px 22px; display: none; align-items: center; justify-content: center; border-radius: 8px; background: var(--primaryColor, var(--primarycolor, rgba(0, 0, 0, .9))); color: #f0f0f0; font-size: 16px; font-weight: 400; line-height: 1.35; text-align: center; white-space: normal; overflow-wrap: anywhere; z-index: 1000; box-shadow: 0 2px 8px rgba(0, 0, 0, .25); }
    .amqShikimoriRussianTitleArrow { position: absolute; right: -10px; top: 50%; transform: translateY(-50%); width: 0; height: 0; border-top: 11px solid transparent; border-bottom: 11px solid transparent; border-left: 10px solid var(--primaryColor, var(--primarycolor, rgba(0, 0, 0, .9))); }
    .amqRussianStatusRow, .amqRussianNoticeRow { padding: 9px; text-align: center; font-weight: 400; }
    .amqRussianNoticeRow { white-space: normal; }
    .amqRussianResultButton { display: block; width: 100%; min-height: 6px; padding: 6px 12px; text-align: center; border: 0; cursor: pointer; font: inherit; font-weight: 400; line-height: 1.35; }
    .amqRussianResultSeparator, .amqRussianResultAmqTitle { opacity: .5; }
    .amqRussianMatch { color: var(--amq-russian-accent); font-weight: 400; }
  `;

  const scriptStyle = document.createElement("style");
  scriptStyle.textContent = SCRIPT_CSS;
  document.head.appendChild(scriptStyle);

})();
