// ==UserScript==
// @name         AMQ Russian DropDown
// @version      1.9.3
// @description  
// @match        https://animemusicquiz.com/*
// @match        https://www.animemusicquiz.com/*
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
  let saveErrorToast;
  let saveErrorToastTimer;
  let activeShikimoriRequest = 0;

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

  const SCROLLBAR_CSS = `
    #amqRussianScrollbarTrack {
      position: absolute;
      z-index: 3;
      top: 0;
      right: 0;
      bottom: 0;
      width: 8px;
      background: transparent;
      pointer-events: none;
    }

    #amqRussianScrollbarThumb {
      position: absolute;
      top: 0;
      right: 1px;
      width: 6px;
      min-height: 20px;
      background: rgba(255, 255, 255, 0.4);
      border-radius: 5px;
      pointer-events: auto;
      cursor: pointer;
      transform: scaleX(1);
      transform-origin: right center;
      transition: transform 120ms ease, background-color 120ms ease;
    }

    #amqRussianScrollbarThumb:hover,
    #amqRussianScrollbarThumb.is-dragging {
      background: color-mix(
        in srgb,
        var(--amq-russian-accent) 40%,
        transparent
      );
      transform: scaleX(1.5);
    }

    #amqRussianListViewport {
      scrollbar-width: none;
      -ms-overflow-style: none;
    }

    #amqRussianListViewport::-webkit-scrollbar {
      display: none;
      width: 0;
      height: 0;
    }
  `;

  const scrollbarStyle = document.createElement("style");
  scrollbarStyle.textContent = SCROLLBAR_CSS;
  document.head.appendChild(scrollbarStyle);

  const panel = document.createElement("div");
  panel.id = "amqRussianTitlePanel";
  panel.style.cssText = [
    "display:none",
    "position:absolute",
    "z-index:999999",
    "border:0",
    "border-radius:8px",
    "box-shadow:0 0 10px 2px #000",
    "overflow:hidden"
  ].join(";");

  const viewport = document.createElement("div");
  viewport.id = "amqRussianListViewport";
  viewport.style.cssText = [
    "position:relative",
    "max-height:260px",
    "overflow-y:auto",
    "overflow-x:hidden",
    "overscroll-behavior:contain"
  ].join(";");

  const scrollbarTrack = document.createElement("div");
  scrollbarTrack.id = "amqRussianScrollbarTrack";

  const scrollbarThumb = document.createElement("div");
  scrollbarThumb.id = "amqRussianScrollbarThumb";
  scrollbarTrack.appendChild(scrollbarThumb);

  panel.append(viewport, scrollbarTrack);

  let debounceTimer;
  let statusTimer;
  let requestId = 0;
  let keyboardIndex = -1;
  let mouseIndex = -1;
  let currentResults = [];
  let dragStartY = 0;
  let dragStartScrollTop = 0;
  let amqTitlesCache = null;
  let amqTitleIndexCache = null;
  let exactAmqTitleIndexCache = null;

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

  function normalize(value) {
    return String(value || "")
      .toLowerCase()
      .replace(/ё/g, "е")
      .normalize("NFKD")
      .replace(/[^\p{L}\p{N}]+/gu, " ")
      .trim()
      .replace(/\b(\d+)(?:st|nd|rd|th)\s+season\b/g, "season $1")
      .replace(/\s+/g, " ");
  }

  function normalizeAmqTitle(value) {
    return String(value || "")
      .toLowerCase()
      .replace(/ё/g, "е")
      .replace(/\b5-toubun\b/g, "gotoubun")
      .replace(/∬/g, " season 2 ")
      .replace(/[∽~]/g, " tilde ")
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

      if (/\s/u.test(character)) {
        while (index + 1 < characters.length && /\s/u.test(characters[index + 1])) {
          index++;
        }
        pattern += "[\\s\\p{P}\\p{S}]+";
      } else if (character === "и") {
        pattern += "[ий]";
      } else if (character === "е" || character === "э" || character === "ё") {
        pattern += "[еэё]";
      } else {
        pattern += character.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
      }
    }

    return pattern;
  }

  function findTitleMatches(title, query) {
    return new RegExp(buildFlexibleTitlePattern(query), "iu").test(title);
  }

  function getSpellingVariants(value, limit = 8) {
    const variants = new Set([value]);
    const queue = [value];

    while (queue.length && variants.size < limit) {
      const current = queue.shift();
      const characters = Array.from(current);

      for (let index = 0; index < characters.length; index++) {
        const character = characters[index];
        const alternatives =
          character === "и"
            ? ["й"]
            : character === "й"
              ? ["и"]
              : character === "е" || character === "э" || character === "ё"
                ? ["е", "э", "ё"].filter(candidate => candidate !== character)
                : [];

        for (const alternative of alternatives) {
          const changed = characters.slice();
          changed[index] = alternative;
          const variant = changed.join("");
          if (!variants.has(variant) && variants.size < limit) {
            variants.add(variant);
            queue.push(variant);
          }
        }
      }
    }

    return [...variants];
  }

  function getCandidateSearchQueries(query) {
    const words = String(query || "")
      .toLowerCase()
      .match(/[\p{L}\p{N}]+/gu) || [];
    const longestWords = [...new Set(words.filter(word => word.length >= 2))]
      .sort((left, right) => right.length - left.length)
      .slice(0, 3);
    const queries = new Set([query.trim()]);

    for (const word of longestWords) {
      for (const variant of getSpellingVariants(word)) {
        queries.add(variant);
      }
    }

    return [...queries].filter(candidate => candidate.length >= 2).slice(0, 25);
  }

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
      const searchTerms = [
        query.trim(),
        ...getSpellingVariants(query.trim(), 8)
      ].filter((term, index, terms) => terms.indexOf(term) === index);
      const candidates = new Map();
      let lastError;

      for (const term of searchTerms) {
        if (term !== query.trim() && candidates.size) break;

        const searchUrl = new URL(`https://${SHIKIMORI_API_HOST}/api/animes`);
        searchUrl.searchParams.set("search", term);
        searchUrl.searchParams.set("limit", "50");

        try {
          const response = await requestJsonWithRetry(searchUrl.href, undefined);
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
        } catch (error) {
          lastError = error;
        }
      }

      if (!candidates.size && lastError) throw lastError;

      const results = [];
      const detailCandidates = [...candidates.values()].slice(0, 12);
      for (const [index, candidate] of detailCandidates.entries()) {
        try {
          if (index > 0) {
            await new Promise(resolve => setTimeout(resolve, 150));
          }
          const anime = extractShikimoriAnime(
            await requestJsonWithRetry(
              `https://${SHIKIMORI_API_HOST}/api/animes/${candidate.id}`,
              undefined
            )
          );
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
        } catch (error) {
          lastError = error;
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
    if (response.inserted) {
      console.info(
        `[AMQ Russian DropDown] Added "${russianTitle}" to the title database (MAL ${malId}).`
      );
    }
  }

  function showSaveErrorToast() {
    if (!saveErrorToast) {
      saveErrorToast = document.createElement("div");
      saveErrorToast.setAttribute("role", "alert");
      saveErrorToast.style.cssText = [
        "position:fixed",
        "right:16px",
        "bottom:16px",
        "z-index:1000000",
        "max-width:360px",
        "padding:10px 14px",
        "border-radius:6px",
        "background:rgba(120,20,20,.95)",
        "color:#fff",
        "font:14px/1.4 sans-serif",
        "box-shadow:0 2px 10px rgba(0,0,0,.4)"
      ].join(";");
      document.body.appendChild(saveErrorToast);
    }

    saveErrorToast.textContent =
      "Не удалось сохранить один или несколько тайтлов Shikimori в базу.";
    saveErrorToast.style.display = "block";
    clearTimeout(saveErrorToastTimer);
    saveErrorToastTimer = setTimeout(() => {
      saveErrorToast.style.display = "none";
    }, 6000);
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
      let hasSaveErrors = false;
      for (const candidate of uniqueCandidates.values()) {
        try {
          await persistDiscoveredShikimoriTitle(candidate, query);
        } catch {
          hasSaveErrors = true;
        }
      }
      if (hasSaveErrors) showSaveErrorToast();
    })();
  }

  async function requestSearchCandidates(
    query,
    onDatabaseResults
  ) {
    const requestCandidate = candidate =>
      requestJson(`${API_BASE}/api/search?q=${encodeURIComponent(candidate)}`);
    let directResults = [];
    let directError;

    try {
      directResults = await requestCandidate(query);
    } catch (error) {
      directError = error;
    }

    let successfulResponses = [];
    const mergedDirectResults = mergeAnimeResults([directResults]);
    if (!hasUsableSearchMatch(mergedDirectResults, query)) {
      const fallbackQueries = getCandidateSearchQueries(query)
        .filter(candidate => candidate !== query.trim());
      const responses = await Promise.allSettled(
        fallbackQueries.map(requestCandidate)
      );
      successfulResponses = responses
        .filter(response => response.status === "fulfilled")
        .map(response => response.value);
    }

    const databaseResults = mergeAnimeResults([
      directResults,
      ...successfulResponses
    ]);
    onDatabaseResults(databaseResults);

    let shikimoriResults = [];
    try {
      shikimoriResults = await requestShikimoriSearchCandidates(query);
    } catch (error) {
      if (!hasUsableSearchMatch(databaseResults, query)) {
        throw directError || error;
      }
    }
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
    tooltip.style.cssText = [
      "position:absolute",
      "left:-253px",
      "top:50%",
      "transform:translateY(-50%)",
      "box-sizing:border-box",
      "width:243px",
      "min-height:79px",
      "padding:12px 22px",
      "display:none",
      "align-items:center",
      "justify-content:center",
      "border-radius:8px",
      "background:var(--primaryColor, var(--primarycolor, rgba(0,0,0,.9)))",
      "color:#f0f0f0",
      "font-size:16px",
      "font-weight:400",
      "line-height:1.35",
      "text-align:center",
      "white-space:normal",
      "overflow-wrap:anywhere",
      "z-index:1000",
      "box-shadow:0 2px 8px rgba(0,0,0,.25)"
    ].join(";");

    const content = document.createElement("span");
    content.className = "amqShikimoriRussianTitleText";

    const arrow = document.createElement("div");
    arrow.setAttribute("aria-hidden", "true");
    arrow.style.cssText = [
      "position:absolute",
      "right:-10px",
      "top:50%",
      "transform:translateY(-50%)",
      "width:0",
      "height:0",
      "border-top:11px solid transparent",
      "border-bottom:11px solid transparent",
      "border-left:10px solid var(--primaryColor, var(--primarycolor, rgba(0,0,0,.9)))"
    ].join(";");
    tooltip.append(content, arrow);

    if (getComputedStyle(container).position === "static") {
      container.style.position = "relative";
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
      wrapper.style.position = "relative";
    }

    if (panel.parentElement !== wrapper) {
      wrapper.appendChild(panel);
    }

    panel.style.left = "0";
    panel.style.top = `${input.offsetHeight}px`;
    panel.style.width = `${wrapper.getBoundingClientRect().width}px`;
    panel.style.font = getComputedStyle(input).font;
    panel.style.fontWeight = "400";
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
    row.style.cssText = "padding:9px;text-align:center;font-weight:400";
    viewport.appendChild(row);

    let dotCount = 1;
    row.textContent = ".".repeat(dotCount);

    statusTimer = setInterval(() => {
      dotCount = (dotCount % 3) + 1;
      row.textContent = ".".repeat(dotCount);
    }, 200);

    positionPanel();
    panel.style.display = "block";
    updateScrollbar();
  }

  function showNotice(message) {
    stopStatusAnimation();
    currentResults = [];
    viewport.replaceChildren();

    const row = document.createElement("div");
    row.style.cssText =
      "padding:9px;text-align:center;font-weight:400;white-space:normal";
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
      match.style.color = COLORS.current.accentColor;
      match.style.fontWeight = "400";
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
    button.style.fontWeight = "400";

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

  function dispatchEnter(input) {
    const options = {
      key: "Enter",
      code: "Enter",
      keyCode: 13,
      which: 13,
      bubbles: true,
      cancelable: true
    };

    input.dispatchEvent(new KeyboardEvent("keydown", options));
    input.dispatchEvent(new KeyboardEvent("keyup", options));
  }

  function chooseNativeAmqOption(result, submitAfterSelection) {
    const input = getInput();
    if (!input) return;

    hidePanel();
    input.value = result.amqValue;
    input.focus();
    input.dispatchEvent(new Event("input", { bubbles: true }));

    let attempts = 0;

    function selectAmqOption() {
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
        option.dispatchEvent(
          new MouseEvent("mousedown", {
            bubbles: true,
            cancelable: true,
            view: unsafeWindow
          })
        );

        if (submitAfterSelection) {
          setTimeout(() => dispatchEnter(input), 0);
        }
        return;
      }

      if (attempts++ < 20) {
        setTimeout(selectAmqOption, 25);
      }
    }

    requestAnimationFrame(selectAmqOption);
  }

  function showResults(results, query) {
    stopStatusAnimation();
    currentResults = results;
    keyboardIndex = -1;
    mouseIndex = -1;
    viewport.replaceChildren();

    if (!results.length) {
      panel.style.display = "none";
      return;
    }

    results.forEach((result, index) => {
      const button = document.createElement("button");
      button.type = "button";
      button.dataset.resultIndex = String(index);
      button.setAttribute("aria-selected", "false");
      button.style.cssText = [
        "display:block",
        "width:100%",
        "min-height:6px",
        "padding:6px 12px",
        "text-align:center",
        "border:0",
        "cursor:pointer",
        "font:inherit",
        "font-weight:400",
        "line-height:1.35"
      ].join(";");

      const russianTitle = document.createElement("span");
      appendHighlightedText(russianTitle, result.russian, query);

      const separator = document.createElement("span");
      separator.textContent = " / ";
      separator.style.opacity = "0.5";

      const amqTitle = document.createElement("span");
      amqTitle.textContent = result.amqTitle;
      amqTitle.style.opacity = "0.5";

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

    const results = [];
    const seen = new Set();

    for (const anime of animes) {
      if (!anime?.russian || !anime?.name) continue;
      if (!findTitleMatches(anime.russian, query)) continue;

      const match =
        getExactAmqTitleIndex()?.get(normalizeAmqTitle(anime.name)) ||
        titleIndex.get(normalize(anime.name)) ||
        { value: anime.name, label: anime.name };
      const key = normalizeAmqTitle(match.value);
      if (seen.has(key)) continue;
      seen.add(key);

      results.push({
        id: anime.id,
        russian: anime.russian,
        amqTitle: match.label,
        amqValue: match.value
      });
    }

    results.sort(
      (a, b) =>
        a.russian.length - b.russian.length ||
        a.russian.localeCompare(b.russian, "ru")
    );

    if (results.length) {
      showResults(results, query);
    } else {
      showNotice("Совпадений в списке названий AMQ не найдено.");
    }
  }

  function search(query, currentRequest) {
    const titleIndex = getAmqTitleIndex();

    if (!titleIndex?.size) {
      showNotice("Список названий AMQ пока недоступен.");
      return;
    }

    showSearching();

    requestSearchCandidates(query, databaseResults => {
      renderSearchResults(databaseResults, query, currentRequest, titleIndex);
    })
      .then(animes => {
        renderSearchResults(animes, query, currentRequest, titleIndex);
      })
      .catch(error => {
        if (currentRequest === requestId) {
          showNotice(`Ошибка поиска: ${error.message}`);
        }
      });
  }

  // Intercept wheel input anywhere inside the dropdown so AMQ volume is unaffected.
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
        event.stopPropagation();
        setKeyboardIndex(keyboardIndex < 0 ? 0 : keyboardIndex + 1);
      } else if (event.key === "ArrowUp") {
        event.preventDefault();
        event.stopPropagation();
        setKeyboardIndex(keyboardIndex < 0 ? 0 : keyboardIndex - 1);
      } else if (event.key === "Enter" && keyboardIndex >= 0) {
        event.preventDefault();
        event.stopPropagation();

        const result = currentResults[keyboardIndex];
        if (result) chooseNativeAmqOption(result, true);
      }
    },
    true
  );

  document.addEventListener("input", event => {
    if (!event.target.matches("#qpAnswerInput")) return;

    clearTimeout(debounceTimer);

    const query = event.target.value.trim();
    const currentRequest = ++requestId;

    currentResults = [];
    keyboardIndex = -1;
    mouseIndex = -1;
    panel.style.display = "none";

    if (query.length < 2 || !/[а-яё]/i.test(query)) return;

    debounceTimer = setTimeout(() => {
      search(query, currentRequest);
    }, 350);
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
})();