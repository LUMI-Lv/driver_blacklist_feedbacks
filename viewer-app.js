(() => {
  const DEFAULT_PAGE_SIZE = 5;
  const CATALOG_FILE = "catalog.json";
  const FETCH_CONCURRENCY = 16;

  const pageBody = document.getElementById("pageBody");
  const pageTitle = document.getElementById("pageTitle");
  const collectionGrid = document.getElementById("collectionGrid");
  const sourceLabel = document.getElementById("sourceLabel");
  const prevBtn = document.getElementById("prevBtn");
  const nextBtn = document.getElementById("nextBtn");
  const firstBtn = document.getElementById("firstBtn");
  const lastBtn = document.getElementById("lastBtn");
  const counter = document.getElementById("counter");
  const pageInput = document.getElementById("pageInput");
  const modal = document.getElementById("modal");
  const modalCard = document.getElementById("modalCard");
  const modalBody = document.getElementById("modalBody");
  const modalTitle = document.getElementById("modalTitle");
  const candidateSearch = document.getElementById("candidateSearch");
  const searchHint = document.getElementById("searchHint");

  let manifest = emptyManifest();
  let baseManifest = emptyManifest();
  let current = 0;
  let currentMessages = [];
  let currentStart = 1;
  /** @type {"none"|"http"} */
  let dataSource = "none";
  let memoryPages = null;
  /** @type {Map<number, any>|null} */
  let basePages = null;
  const pageCache = new Map();
  let loadSeq = 0;
  let searchQuery = "";
  let searchTimer = 0;
  let searching = false;

  function emptyManifest() {
    return {
      pageSize: DEFAULT_PAGE_SIZE,
      pageCount: 0,
      users: 0,
      messages: 0,
      candidates: 0,
      requests: 0,
      feedbacks: 0,
      oldestTimestamp: "",
      newestTimestamp: ""
    };
  }

  function escapeHtml(value) {
    return String(value ?? "")
      .replaceAll("&", "&amp;")
      .replaceAll("<", "&lt;")
      .replaceAll(">", "&gt;")
      .replaceAll('"', "&quot;");
  }

  function renderSourceLabel() {
    const m = baseManifest || emptyManifest();
    if (dataSource === "http") {
      const n = m.messages || 0;
      sourceLabel.textContent = "Source: HTTP catalog (" + n + " message" + (n === 1 ? "" : "s") + ")";
    } else {
      sourceLabel.textContent = "No data — serve this folder over HTTP with catalog.json";
    }
  }

  function timestampRange(oldest, newest) {
    const from = oldest || "";
    const to = newest || "";
    if (!from && !to) return "—";
    if (!from) return to;
    if (!to) return from;
    if (from === to) return from;
    return from + " – " + to;
  }

  function renderCollectionInfo() {
    const m = baseManifest || emptyManifest();
    const fields = [
      ["Users", m.users ?? 0],
      ["Messages", m.messages ?? 0],
      ["Candidates", m.candidates ?? 0],
      ["Requests", m.requests ?? 0],
      ["Feedbacks", m.feedbacks ?? 0],
      ["Timestamps", timestampRange(m.oldestTimestamp, m.newestTimestamp)]
    ];
    collectionGrid.innerHTML = fields
      .map(([label, value]) =>
        `<div><dt>${escapeHtml(label)}</dt><dd>${escapeHtml(value)}</dd></div>`
      ).join("");
    renderSourceLabel();
  }

  function normalizeName(value) {
    return String(value || "")
      .trim()
      .toLowerCase()
      .replaceAll("ё", "е")
      .replace(/[ʼ'`´]/g, "")
      .replace(/[-_/.,]+/g, " ")
      .replace(/\s+/g, " ");
  }

  function tokenizeQuery(query) {
    return normalizeName(query).split(" ").filter(Boolean);
  }

  function levenshtein(a, b) {
    if (a === b) return 0;
    if (!a.length) return b.length;
    if (!b.length) return a.length;
    if (a.length > b.length) {
      const tmp = a;
      a = b;
      b = tmp;
    }
    const prev = new Array(a.length + 1);
    for (let i = 0; i <= a.length; i += 1) prev[i] = i;
    for (let j = 1; j <= b.length; j += 1) {
      let prevDiag = prev[0];
      prev[0] = j;
      for (let i = 1; i <= a.length; i += 1) {
        const temp = prev[i];
        const cost = a.charCodeAt(i - 1) === b.charCodeAt(j - 1) ? 0 : 1;
        prev[i] = Math.min(prev[i] + 1, prev[i - 1] + 1, prevDiag + cost);
        prevDiag = temp;
      }
    }
    return prev[a.length];
  }

  function maxEditDistance(token) {
    const len = token.length;
    if (len <= 2) return 0;
    if (len <= 5) return 1;
    return 2;
  }

  function tokenSimilarity(queryToken, candidatePart) {
    if (!queryToken || !candidatePart) return 0;
    if (queryToken === candidatePart) return 1;
    if (candidatePart.startsWith(queryToken)) {
      return 0.96 - Math.min(0.1, (candidatePart.length - queryToken.length) * 0.01);
    }
    if (queryToken.startsWith(candidatePart) && candidatePart.length >= 3) {
      return 0.9;
    }
    if (candidatePart.includes(queryToken) && queryToken.length >= 3) {
      return 0.84;
    }

    const allowed = maxEditDistance(queryToken);
    if (allowed <= 0) return 0;

    const fullDist = levenshtein(queryToken, candidatePart);
    if (fullDist <= allowed) {
      return Math.max(0.55, 1 - fullDist / Math.max(queryToken.length, candidatePart.length));
    }

    if (candidatePart.length > queryToken.length) {
      const window = candidatePart.slice(0, queryToken.length);
      const prefixDist = levenshtein(queryToken, window);
      if (prefixDist <= allowed) {
        return Math.max(0.5, 0.92 - prefixDist / queryToken.length);
      }
      // slide a same-length window for mid-string typos on longer parts
      for (let i = 1; i <= candidatePart.length - queryToken.length; i += 1) {
        const slice = candidatePart.slice(i, i + queryToken.length);
        const dist = levenshtein(queryToken, slice);
        if (dist <= allowed) {
          return Math.max(0.48, 0.86 - dist / queryToken.length);
        }
      }
    }

    return 0;
  }

  function scoreCandidateName(msg, queryTokens) {
    const parts = [
      normalizeName(msg.subjectLastName),
      normalizeName(msg.subjectFirstName),
      normalizeName(msg.subjectPatronymic)
    ].filter(Boolean);

    if (!parts.length || !queryTokens.length) {
      return { score: 0, exact: false };
    }

    const used = new Set();
    const tokenScores = [];

    for (const token of queryTokens) {
      let best = 0;
      let bestIdx = -1;
      for (let i = 0; i < parts.length; i += 1) {
        if (used.has(i)) continue;
        const sim = tokenSimilarity(token, parts[i]);
        if (sim > best) {
          best = sim;
          bestIdx = i;
        }
      }

      if (bestIdx < 0 || best <= 0) {
        const full = parts.join(" ");
        const fullSim = tokenSimilarity(token, full);
        if (fullSim <= 0) {
          return { score: 0, exact: false };
        }
        tokenScores.push(fullSim);
        continue;
      }

      used.add(bestIdx);
      tokenScores.push(best);
    }

    const score = tokenScores.reduce((sum, value) => sum + value, 0) / tokenScores.length;
    const exact = tokenScores.every((value) => value >= 0.999);
    return { score, exact };
  }

  function isFeedbackMessage(msg) {
    return messageTypesOf(msg.messageType).includes("feedback");
  }

  function collectAllMessages() {
    const out = [];
    if (!basePages || !baseManifest) return out;
    const pageCount = baseManifest.pageCount || 0;
    for (let page = 1; page <= pageCount; page += 1) {
      const data = basePages.get(page);
      if (data && Array.isArray(data.messages)) {
        out.push(...data.messages);
      }
    }
    return out;
  }

  function paginateMessages(messages, pageSize) {
    const size = pageSize > 0 ? pageSize : DEFAULT_PAGE_SIZE;
    const pageCount = messages.length === 0 ? 0 : Math.ceil(messages.length / size);
    const pageMap = new Map();
    for (let page = 0; page < pageCount; page += 1) {
      const from = page * size;
      pageMap.set(page + 1, {
        page: page + 1,
        start: from + 1,
        messages: messages.slice(from, from + size)
      });
    }
    return { pageCount, pageMap, pageSize: size };
  }

  function activateView(nextManifest, pagesMap) {
    manifest = nextManifest || emptyManifest();
    memoryPages = pagesMap;
    pageCache.clear();
    if (pagesMap) {
      for (const [pageNumber, data] of pagesMap.entries()) {
        pageCache.set(pageNumber, data);
      }
    }
    showPage(0);
  }

  function setSearchHint(text) {
    if (searchHint) searchHint.textContent = text || "";
  }

  function applySearch(rawQuery) {
    searchQuery = String(rawQuery || "").trim();
    const tokens = tokenizeQuery(searchQuery);
    if (!tokens.length) {
      searching = false;
      setSearchHint("");
      activateView(baseManifest, basePages);
      return;
    }
    if (!basePages || !(baseManifest.pageCount > 0)) {
      searching = true;
      setSearchHint("No data to search");
      activateView({ ...baseManifest, pageCount: 0, messages: 0, pageSize: baseManifest.pageSize || DEFAULT_PAGE_SIZE }, new Map());
      return;
    }

    const MATCH_THRESHOLD = 0.55;
    const scored = [];
    for (const msg of collectAllMessages()) {
      const result = scoreCandidateName(msg, tokens);
      if (result.score >= MATCH_THRESHOLD) {
        scored.push({ msg, score: result.score, exact: result.exact });
      }
    }

    scored.sort((left, right) => {
      if (left.exact !== right.exact) return left.exact ? -1 : 1;
      if (left.exact && right.exact) {
        const leftFeedback = isFeedbackMessage(left.msg) ? 1 : 0;
        const rightFeedback = isFeedbackMessage(right.msg) ? 1 : 0;
        if (leftFeedback !== rightFeedback) return rightFeedback - leftFeedback;
      }
      if (right.score !== left.score) return right.score - left.score;
      const byName = subjectDisplay(left.msg).localeCompare(subjectDisplay(right.msg), undefined, {
        sensitivity: "base"
      });
      if (byName !== 0) return byName;
      return compareTimestamp(left.msg.timestamp, right.msg.timestamp);
    });

    const matched = scored.map((entry) => entry.msg);
    const pageSize = baseManifest.pageSize || DEFAULT_PAGE_SIZE;
    const paged = paginateMessages(matched, pageSize);
    searching = true;
    const exactCount = scored.filter((entry) => entry.exact).length;
    setSearchHint(
      matched.length
        ? `${matched.length} match${matched.length === 1 ? "" : "es"}`
          + (exactCount ? ` (${exactCount} exact)` : "")
        : "No matches"
    );
    activateView({
      ...baseManifest,
      pageSize: paged.pageSize,
      pageCount: paged.pageCount,
      messages: matched.length
    }, paged.pageMap);
  }

  function scheduleSearch(rawQuery) {
    window.clearTimeout(searchTimer);
    searchTimer = window.setTimeout(() => applySearch(rawQuery), 180);
  }

  function initials(name) {
    const parts = String(name || "?").trim().split(/\s+/).filter(Boolean);
    if (!parts.length) return "?";
    return parts.slice(0, 2).map((p) => p[0].toUpperCase()).join("");
  }

  function imagesOf(msg) {
    if (Array.isArray(msg.baloons)) return msg.baloons.filter(Boolean);
    return [];
  }

  function subjectParts(msg) {
    return {
      lastName: msg.subjectLastName || "",
      firstName: msg.subjectFirstName || "",
      patronymic: msg.subjectPatronymic || ""
    };
  }

  function subjectDisplay(msg) {
    const parts = subjectParts(msg);
    return [parts.lastName, parts.firstName, parts.patronymic].filter(Boolean).join(" ");
  }

  function messageTypesOf(type) {
    const raw = String(type || "flood");
    const parts = raw.split(/[,+/|]+/).map((part) => part.trim().toLowerCase()).filter(Boolean);
    return parts.length ? parts : ["flood"];
  }

  function renderTypePill(type) {
    const pills = messageTypesOf(type).map((safe) =>
      `<span class="type-pill ${escapeHtml(safe)}">${escapeHtml(safe)}</span>`
    );
    return `<span class="type-pills">${pills.join("")}</span>`;
  }

  function authorLabel(msg) {
    return (msg && msg.activePhone) || "Unknown contact";
  }

  function renderUserIcon(msg, msgIndex) {
    const label = authorLabel(msg);
    const fallback = escapeHtml(initials(label));
    return `
      <button class="user-btn" type="button"
        data-msg="${msgIndex}"
        title="Open contact: ${escapeHtml(label)}"
        aria-label="Open contact ${escapeHtml(label)}">
        <span class="initials">${fallback}</span>
      </button>`;
  }

  function renderReply(msg) {
    if (!msg.replyToMessage) return "";
    return `<div class="reply-quote">${escapeHtml(msg.replyToMessage || "")}</div>`;
  }

  function setNavDisabled(disabled) {
    firstBtn.disabled = disabled || current === 0;
    prevBtn.disabled = disabled || current === 0;
    const last = !manifest || manifest.pageCount < 1
      ? true
      : current >= manifest.pageCount - 1;
    nextBtn.disabled = disabled || last;
    lastBtn.disabled = disabled || last;
    pageInput.disabled = disabled || !manifest || manifest.pageCount < 1;
  }

  function loadPageData(pageNumber) {
    if (pageCache.has(pageNumber)) {
      return pageCache.get(pageNumber);
    }
    if (memoryPages && memoryPages.has(pageNumber)) {
      const data = memoryPages.get(pageNumber);
      pageCache.set(pageNumber, data);
      return data;
    }
    throw new Error("Page " + pageNumber + " is not loaded");
  }

  function renderPage() {
    if (!manifest || manifest.pageCount < 1 || !currentMessages.length) {
      pageTitle.textContent = searching ? "Matches (0)" : "Messages (0)";
      pageBody.innerHTML = `<div class="empty">${searching ? "No matching candidates" : "No messages"}</div>`;
      counter.textContent = "0 / 0";
      pageInput.value = 1;
      pageInput.max = 1;
      setNavDisabled(true);
      return;
    }

    const total = manifest.messages || 0;
    const start = currentStart;
    const end = currentStart + currentMessages.length - 1;
    pageTitle.textContent = searching
      ? `Matches ${start}–${end} of ${total}`
      : `Messages ${start}–${end} of ${total}`;
    counter.textContent = `${current + 1} / ${manifest.pageCount}`;
    pageInput.value = current + 1;
    pageInput.max = manifest.pageCount;
    setNavDisabled(false);

    const rows = currentMessages.map((msg, msgIndex) => {
      const balloons = imagesOf(msg);
      const activePhone = msg.activePhone || "";
      const subject = subjectParts(msg);
      return `
        <tr>
          <td>
            <div class="user-cell">
              <div class="user-avatar">
                ${renderUserIcon(msg, msgIndex)}
                ${activePhone
                  ? `<div class="active-phone"><b>${escapeHtml(activePhone)}</b></div>`
                  : `<div class="phones">no phone</div>`}
              </div>
            </div>
          </td>
          <td>${escapeHtml(msg.timestamp || "—")}</td>
          <td>${renderTypePill(msg.messageType)}</td>
          <td class="subject-part">${escapeHtml(subject.lastName || "—")}</td>
          <td class="subject-part">${escapeHtml(subject.firstName || "—")}</td>
          <td class="subject-part">${escapeHtml(subject.patronymic || "—")}</td>
          <td class="message">${renderReply(msg)}${escapeHtml(msg.message || "")}</td>
          <td>
            ${balloons.length
              ? `<div class="balloon-cell">${balloons.map((shot, imgIndex) => `
                   <button class="balloon-btn" type="button"
                     data-msg="${msgIndex}" data-img="${imgIndex}"
                     title="Open image ${imgIndex + 1} of ${balloons.length}"
                     aria-label="Open image ${imgIndex + 1} of ${balloons.length}">
                     <img class="balloon-thumb" src="${escapeHtml(shot)}" alt="image ${imgIndex + 1}">
                     ${balloons.length > 1 ? `<span class="ordinal">${imgIndex + 1}</span>` : ""}
                   </button>`).join("")}</div>`
              : "—"}
          </td>
        </tr>`;
    }).join("");

    pageBody.innerHTML = `
      <div class="table-wrap">
        <table>
          <thead>
            <tr>
              <th>Contact</th>
              <th>Timestamp</th>
              <th>Type</th>
              <th>Last name</th>
              <th>First name</th>
              <th>Patronymic</th>
              <th>Message</th>
              <th>Images</th>
            </tr>
          </thead>
          <tbody>${rows}</tbody>
        </table>
      </div>`;
  }

  async function showPage(index) {
    if (!manifest || manifest.pageCount < 1) {
      current = 0;
      currentMessages = [];
      currentStart = 1;
      renderPage();
      return;
    }
    const seq = ++loadSeq;
    current = Math.min(Math.max(index, 0), manifest.pageCount - 1);
    setNavDisabled(true);
    try {
      const data = loadPageData(current + 1);
      if (seq !== loadSeq) return;
      currentMessages = Array.isArray(data.messages) ? data.messages : [];
      currentStart = Number(data.start) || (current * (manifest.pageSize || DEFAULT_PAGE_SIZE) + 1);
      renderPage();
      window.scrollTo({ top: 0, behavior: "smooth" });
    } catch (error) {
      if (seq !== loadSeq) return;
      pageBody.innerHTML = `<div class="empty">Failed to load page:
        ${escapeHtml(error && error.message ? error.message : error)}</div>`;
      setNavDisabled(false);
    }
  }

  function applyDataset(nextManifest, pagesMap, source) {
    baseManifest = nextManifest || emptyManifest();
    basePages = pagesMap;
    dataSource = source;
    searchQuery = "";
    searching = false;
    if (candidateSearch) candidateSearch.value = "";
    setSearchHint("");
    renderCollectionInfo();
    activateView(baseManifest, basePages);
  }

  function applyEmpty() {
    applyDataset(emptyManifest(), null, "none");
  }

  function isMessageEntity(obj) {
    return obj && typeof obj === "object"
      && typeof obj.userHash === "string"
      && ("text" in obj || "message" in obj)
      && !Array.isArray(obj.messages);
  }

  function isUserEntity(obj) {
    return obj && typeof obj === "object"
      && typeof obj.name === "string"
      && Array.isArray(obj.phones)
      && !isMessageEntity(obj);
  }

  function isCandidateEntity(obj) {
    return obj && typeof obj === "object"
      && "lastName" in obj
      && "firstName" in obj
      && !("userHash" in obj)
      && !Array.isArray(obj.messages);
  }

  function compareTimestamp(left, right) {
    const a = left == null ? "" : String(left).trim();
    const b = right == null ? "" : String(right).trim();
    const aBlank = !a || a.toLowerCase() === "unknown";
    const bBlank = !b || b.toLowerCase() === "unknown";
    if (aBlank && bBlank) return 0;
    if (aBlank) return 1;
    if (bBlank) return -1;
    return a < b ? -1 : a > b ? 1 : 0;
  }

  function enrichMessage(msg, usersByHash, candidatesByHash) {
    const user = usersByHash.get(msg.userHash) || {};
    const candidate = msg.candidateHash ? candidatesByHash.get(msg.candidateHash) : null;
    return {
      hash: msg.hash || "",
      timestamp: msg.timestamp || "",
      message: msg.text != null ? msg.text : (msg.message || ""),
      baloonMessage: msg.baloonMessage || "",
      messageType: msg.messageType || "",
      userName: user.name || "",
      userScreenshot: user.screenshot || "",
      activePhone: user.activePhone || "",
      userPhones: Array.isArray(user.phones) ? user.phones : [],
      subjectLastName: candidate ? (candidate.lastName || "") : "",
      subjectFirstName: candidate ? (candidate.firstName || "") : "",
      subjectPatronymic: candidate ? (candidate.patronymic || "") : "",
      replyToUserName: msg.replyToUserName || "",
      replyToMessage: msg.replyToMessage || "",
      baloons: Array.isArray(msg.baloons) ? msg.baloons : []
    };
  }

  function buildFromEntities(users, messages, candidates, pageSize) {
    const usersByHash = new Map();
    for (const user of users) {
      if (user && user.hash) usersByHash.set(user.hash, user);
    }
    const candidatesByHash = new Map();
    for (const candidate of candidates) {
      if (candidate && candidate.hash) candidatesByHash.set(candidate.hash, candidate);
    }

    const sorted = messages.slice().sort((left, right) => {
      const byTs = compareTimestamp(left.timestamp, right.timestamp);
      if (byTs !== 0) return byTs;
      return String(left.hash || "").localeCompare(String(right.hash || ""));
    });

    let requests = 0;
    let feedbacks = 0;
    for (const message of sorted) {
      const types = messageTypesOf(message.messageType);
      if (types.includes("request")) requests += 1;
      if (types.includes("feedback")) feedbacks += 1;
    }

    const size = pageSize > 0 ? pageSize : DEFAULT_PAGE_SIZE;
    const pageCount = sorted.length === 0 ? 0 : Math.ceil(sorted.length / size);
    const pageMap = new Map();
    for (let page = 0; page < pageCount; page += 1) {
      const from = page * size;
      const slice = sorted.slice(from, from + size);
      pageMap.set(page + 1, {
        page: page + 1,
        start: from + 1,
        messages: slice.map((msg) => enrichMessage(msg, usersByHash, candidatesByHash))
      });
    }

    return {
      manifest: {
        pageSize: size,
        pageCount,
        users: usersByHash.size,
        messages: sorted.length,
        candidates: candidatesByHash.size,
        requests,
        feedbacks,
        oldestTimestamp: sorted.length ? (sorted[0].timestamp || "") : "",
        newestTimestamp: sorted.length ? (sorted[sorted.length - 1].timestamp || "") : ""
      },
      pageMap
    };
  }

  function classifyObject(obj, hint) {
    if (hint === "user" || isUserEntity(obj)) return "user";
    if (hint === "message" || isMessageEntity(obj)) return "message";
    if (hint === "candidate" || isCandidateEntity(obj)) return "candidate";
    return "";
  }

  async function ingestParsedObjects(objects, source) {
    const users = [];
    const messages = [];
    const candidates = [];
    for (const { obj, hint } of objects) {
      const kind = classifyObject(obj, hint);
      if (kind === "user") users.push(obj);
      else if (kind === "message") messages.push(obj);
      else if (kind === "candidate") candidates.push(obj);
    }
    if (!users.length && !messages.length && !candidates.length) {
      pageBody.innerHTML = `<div class="empty">No recognizable DB entity JSON found</div>`;
      return false;
    }
    const built = buildFromEntities(users, messages, candidates, DEFAULT_PAGE_SIZE);
    applyDataset(built.manifest, built.pageMap, source);
    return true;
  }

  function catalogEntries(catalog) {
    const groups = [
      ["users", "user"],
      ["messages", "message"],
      ["candidates", "candidate"]
    ];
    const entries = [];
    for (const [property, hint] of groups) {
      const paths = catalog && catalog[property];
      if (!Array.isArray(paths)) {
        throw new Error(`Catalog property "${property}" must be an array`);
      }
      for (const path of paths) {
        if (typeof path !== "string" || !path.toLowerCase().endsWith(".json")) {
          throw new Error(`Invalid ${property} path in catalog`);
        }
        entries.push({ path, hint });
      }
    }
    return entries;
  }

  function resourceUrl(relativePath) {
    const encodedPath = relativePath
      .replaceAll("\\", "/")
      .split("/")
      .map((segment) => encodeURIComponent(segment))
      .join("/");
    return new URL(encodedPath, document.baseURI);
  }

  async function loadFromCatalog() {
    let response;
    try {
      response = await fetch(CATALOG_FILE, { cache: "no-store" });
    } catch {
      return false;
    }
    if (!response.ok) {
      return false;
    }

    try {
      const entries = catalogEntries(await response.json());
      pageBody.innerHTML = `<div class="empty">Loading ${entries.length} JSON resource(s)…</div>`;
      const objects = [];
      let failed = 0;
      let next = 0;
      let completed = 0;

      async function worker() {
        while (next < entries.length) {
          const entry = entries[next++];
          try {
            const entityResponse = await fetch(resourceUrl(entry.path), { cache: "no-store" });
            if (!entityResponse.ok) {
              throw new Error(`HTTP ${entityResponse.status}`);
            }
            objects.push({ obj: await entityResponse.json(), hint: entry.hint });
          } catch (error) {
            failed += 1;
            console.warn("Could not load DB resource", entry.path, error);
          }
          completed += 1;
          if (completed % 100 === 0 || completed === entries.length) {
            pageBody.innerHTML = `<div class="empty">Loading DB resources: ${completed} / ${entries.length}…</div>`;
          }
        }
      }

      const workerCount = Math.min(FETCH_CONCURRENCY, Math.max(entries.length, 1));
      await Promise.all(Array.from({ length: workerCount }, () => worker()));
      const ok = await ingestParsedObjects(objects, "http");
      if (!ok) {
        pageBody.innerHTML = `<div class="empty">Catalog contained no readable DB entities`
          + (failed ? ` (${failed} failed resource(s))` : "") + `</div>`;
      } else if (failed) {
        console.warn(`Loaded HTTP catalog with ${failed} failed resource(s)`);
      }
      return ok;
    } catch (error) {
      pageBody.innerHTML = `<div class="empty">Could not load ${escapeHtml(CATALOG_FILE)}:
        ${escapeHtml(error && error.message ? error.message : error)}</div>`;
      return false;
    }
  }

  function openProfile(msgIndex) {
    const msg = currentMessages[msgIndex];
    if (!msg) return;
    const subject = subjectParts(msg);
    modalCard.classList.remove("wide");
    modalTitle.textContent = authorLabel(msg);
    modalBody.innerHTML = `
      <dl class="meta">
        <div><dt>Active phone</dt><dd><b>${escapeHtml(msg.activePhone || "—")}</b></dd></div>
        <div><dt>Type</dt><dd>${renderTypePill(msg.messageType)}</dd></div>
        <div><dt>Last name</dt><dd>${escapeHtml(subject.lastName || "—")}</dd></div>
        <div><dt>First name</dt><dd>${escapeHtml(subject.firstName || "—")}</dd></div>
        <div><dt>Patronymic</dt><dd>${escapeHtml(subject.patronymic || "—")}</dd></div>
        <div><dt>Balloon message</dt><dd style="white-space:pre-wrap">${escapeHtml(msg.baloonMessage || "—")}</dd></div>
        <div><dt>Message hash</dt><dd>${escapeHtml(msg.hash || "—")}</dd></div>
      </dl>
    `;
    modal.classList.add("open");
  }

  let gallery = { shots: [], index: 0, msg: null };

  function openBalloon(msgIndex, imgIndex) {
    const msg = currentMessages[msgIndex];
    if (!msg) return;
    const shots = imagesOf(msg);
    if (!shots.length) return;
    gallery = { shots, index: Math.min(Math.max(imgIndex || 0, 0), shots.length - 1), msg };
    renderGallery();
    modal.classList.add("open");
  }

  function renderGallery() {
    const { shots, index, msg } = gallery;
    if (!msg) return;
    modalCard.classList.add("wide");
    modalTitle.textContent = shots.length > 1
      ? `Images (${index + 1} / ${shots.length})`
      : "Image";
    modalBody.innerHTML = `
      <img class="balloon-shot" src="${escapeHtml(shots[index])}" alt="Message image">
      ${shots.length > 1
        ? `<div class="gallery-nav">
             <button id="galleryPrev" type="button">← Prev</button>
             <span>${index + 1} / ${shots.length}</span>
             <button id="galleryNext" type="button">Next →</button>
           </div>`
        : ""}
      <dl class="meta">
        <div><dt>Contact</dt><dd>${escapeHtml(authorLabel(msg))}</dd></div>
        <div><dt>Type</dt><dd>${renderTypePill(msg.messageType)}</dd></div>
        <div><dt>Subject</dt><dd>${escapeHtml(subjectDisplay(msg) || "—")}</dd></div>
        <div><dt>Message</dt><dd style="white-space:pre-wrap">${escapeHtml(msg.message || msg.baloonMessage || "—")}</dd></div>
      </dl>
    `;
    const prev = document.getElementById("galleryPrev");
    const next = document.getElementById("galleryNext");
    if (prev) prev.addEventListener("click", () => stepGallery(-1));
    if (next) next.addEventListener("click", () => stepGallery(1));
  }

  function stepGallery(delta) {
    if (gallery.shots.length < 2) return;
    gallery.index = (gallery.index + delta + gallery.shots.length) % gallery.shots.length;
    renderGallery();
  }

  function closeModal() {
    modal.classList.remove("open");
    gallery = { shots: [], index: 0, msg: null };
  }

  firstBtn.addEventListener("click", () => showPage(0));
  lastBtn.addEventListener("click", () => showPage((manifest?.pageCount || 1) - 1));
  prevBtn.addEventListener("click", () => showPage(current - 1));
  nextBtn.addEventListener("click", () => showPage(current + 1));
  pageInput.addEventListener("change", () => {
    const value = Number(pageInput.value);
    if (Number.isFinite(value)) {
      showPage(value - 1);
    }
  });
  if (candidateSearch) {
    candidateSearch.addEventListener("input", () => {
      scheduleSearch(candidateSearch.value);
    });
    candidateSearch.addEventListener("keydown", (e) => {
      if (e.key === "Escape") {
        candidateSearch.value = "";
        applySearch("");
        candidateSearch.blur();
      }
    });
  }
  document.getElementById("closeModal").addEventListener("click", closeModal);
  modal.addEventListener("click", (e) => {
    if (e.target === modal) closeModal();
  });
  document.addEventListener("keydown", (e) => {
    if (e.key === "Escape") closeModal();
    const typing = e.target === candidateSearch
      || (e.target instanceof HTMLElement && e.target.closest("input, textarea"));
    if (typing) return;
    const inGallery = modal.classList.contains("open") && gallery.shots.length > 1;
    if (e.key === "ArrowLeft") inGallery ? stepGallery(-1) : showPage(current - 1);
    if (e.key === "ArrowRight") inGallery ? stepGallery(1) : showPage(current + 1);
  });
  pageBody.addEventListener("click", (e) => {
    const userBtn = e.target.closest(".user-btn");
    if (userBtn) {
      openProfile(Number(userBtn.dataset.msg));
      return;
    }
    const balloonBtn = e.target.closest(".balloon-btn");
    if (balloonBtn) {
      openBalloon(Number(balloonBtn.dataset.msg), Number(balloonBtn.dataset.img));
    }
  });
  pageBody.addEventListener("error", (e) => {
    const img = e.target;
    if (!(img instanceof HTMLImageElement) || !img.matches(".user-btn img")) return;
    const span = document.createElement("span");
    span.className = "initials";
    span.textContent = img.dataset.fallback || "?";
    img.replaceWith(span);
  }, true);

  (async function boot() {
    applyEmpty();
    if (!(await loadFromCatalog())) {
      applyEmpty();
      pageBody.innerHTML = `<div class="empty">Could not load ${escapeHtml(CATALOG_FILE)} — serve this folder over HTTP</div>`;
    }
  })();
})();
