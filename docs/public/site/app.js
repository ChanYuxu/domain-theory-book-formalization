import * as pdfjsLib from "./vendor/pdfjs/pdf.mjs";

pdfjsLib.GlobalWorkerOptions.workerSrc = "./vendor/pdfjs/pdf.worker.mjs";

const MAX_RENDER_SCALE = 1.4;
const SPLIT_STORAGE_KEY = "domain-theory-public-reader-split-v1";
const state = {
  manifest: null,
  chapterMeta: null,
  chapterData: null,
  pdf: null,
  selectedId: "",
  declarationIndex: 0,
  query: "",
  linkById: new Map(),
  renderToken: 0,
  dragging: false,
  resizeTimer: 0,
  toastTimer: 0,
};

const workspace = document.getElementById("workspace");
const chapterSelect = document.getElementById("chapterSelect");
const itemSearch = document.getElementById("itemSearch");
const itemNav = document.getElementById("itemNav");
const pdfScroll = document.getElementById("pdfScroll");
const pdfStatus = document.getElementById("pdfStatus");
const splitter = document.getElementById("splitter");
const buildMeta = document.getElementById("buildMeta");
const repositoryLink = document.getElementById("repositoryLink");
const itemKicker = document.getElementById("itemKicker");
const itemTitle = document.getElementById("itemTitle");
const itemSummary = document.getElementById("itemSummary");
const itemMetadata = document.getElementById("itemMetadata");
const declarationControl = document.getElementById("declarationControl");
const declarationSelect = document.getElementById("declarationSelect");
const sourceLocation = document.getElementById("sourceLocation");
const githubSource = document.getElementById("githubSource");
const copyCode = document.getElementById("copyCode");
const codeView = document.getElementById("codeView");
const codeScroll = document.getElementById("codeScroll");
const toast = document.getElementById("toast");

function hashState() {
  const params = new URLSearchParams(location.hash.replace(/^#/, ""));
  return {
    chapter: Number(params.get("chapter")),
    item: params.get("item") || "",
  };
}

function updateHash() {
  if (!state.chapterMeta) return;
  const params = new URLSearchParams({ chapter: String(state.chapterMeta.number) });
  if (state.selectedId) params.set("item", state.selectedId);
  history.replaceState(null, "", `#${params.toString()}`);
}

function itemById(id) {
  return state.chapterData?.items.find((item) => item.id === id) || null;
}

function normalizeDestination(destination) {
  if (typeof destination === "string") return destination;
  if (Array.isArray(destination) && typeof destination[0] === "string") {
    return destination[0];
  }
  return "";
}

function showToast(message) {
  clearTimeout(state.toastTimer);
  toast.textContent = message;
  toast.classList.add("visible");
  state.toastTimer = window.setTimeout(() => toast.classList.remove("visible"), 1800);
}

function setLoading(message) {
  pdfScroll.innerHTML = "";
  const loading = document.createElement("div");
  loading.className = "loading-state";
  const bar = document.createElement("span");
  bar.className = "loading-bar";
  bar.setAttribute("aria-hidden", "true");
  const label = document.createElement("span");
  label.textContent = message;
  loading.append(bar, label);
  pdfScroll.appendChild(loading);
}

function showError(error) {
  pdfStatus.textContent = "Unavailable";
  pdfScroll.innerHTML = "";
  const panel = document.createElement("div");
  panel.className = "error-state";
  panel.textContent = error instanceof Error ? error.message : String(error);
  pdfScroll.appendChild(panel);
}

function renderItemNav() {
  itemNav.innerHTML = "";
  if (!state.chapterData) return;
  const query = state.query.trim().toLowerCase();
  const items = state.chapterData.items.filter((item) => {
    const declarationNames = item.declarations.map((declaration) => declaration.name);
    const text = [item.number, item.kind, item.title, item.summary, ...declarationNames]
      .join(" ")
      .toLowerCase();
    return !query || text.includes(query);
  });

  if (!items.length) {
    const empty = document.createElement("div");
    empty.className = "nav-empty";
    empty.textContent = "No matching items.";
    itemNav.appendChild(empty);
    return;
  }

  const fragment = document.createDocumentFragment();
  for (const item of items) {
    const button = document.createElement("button");
    button.type = "button";
    button.className = `item-button${item.id === state.selectedId ? " active" : ""}`;
    button.dataset.id = item.id;

    const number = document.createElement("span");
    number.className = "item-number";
    number.textContent = item.number;
    const title = document.createElement("span");
    title.className = "item-name";
    title.textContent = item.title;
    button.append(number, title);
    fragment.appendChild(button);
  }
  itemNav.appendChild(fragment);
}

function metadataChip(label, status = false) {
  const chip = document.createElement("span");
  chip.className = `metadata-chip${status ? " status" : ""}`;
  chip.textContent = label;
  return chip;
}

function renderMetadata(item) {
  itemMetadata.innerHTML = "";
  itemMetadata.append(
    metadataChip(item.kind || "Book item"),
    metadataChip(`Section ${item.section}`),
    metadataChip(`Source PDF p. ${item.sourcePdfPage}`),
  );
  if (item.formalizationStatus) {
    itemMetadata.append(metadataChip(item.formalizationStatus, true));
  }
  if (item.proofBoundaryStatus) {
    itemMetadata.append(metadataChip(item.proofBoundaryStatus, true));
  }
}

function renderDeclaration() {
  const item = itemById(state.selectedId);
  const declaration = item?.declarations[state.declarationIndex];
  if (!item || !declaration) {
    sourceLocation.textContent = "";
    githubSource.hidden = true;
    copyCode.disabled = true;
    codeView.textContent = "-- Select a mapped book item.";
    return;
  }
  sourceLocation.textContent = `${declaration.file}:${declaration.startLine}-${declaration.endLine}`;
  sourceLocation.title = sourceLocation.textContent;
  githubSource.href = declaration.githubUrl;
  githubSource.hidden = false;
  copyCode.disabled = false;
  codeView.textContent = declaration.code;
  codeScroll.scrollTop = 0;
  codeScroll.scrollLeft = 0;
}

function renderItem(item) {
  if (!item) return;
  itemKicker.textContent = item.number;
  itemTitle.textContent = item.title;
  itemSummary.textContent = [item.summary, item.reviewNote].filter(Boolean).join(" ");
  renderMetadata(item);

  state.declarationIndex = Math.min(
    state.declarationIndex,
    Math.max(0, item.declarations.length - 1),
  );
  declarationSelect.innerHTML = "";
  for (const [index, declaration] of item.declarations.entries()) {
    const option = document.createElement("option");
    option.value = String(index);
    option.textContent = declaration.name;
    declarationSelect.appendChild(option);
  }
  declarationSelect.value = String(state.declarationIndex);
  declarationControl.hidden = item.declarations.length <= 1;
  renderDeclaration();
}

function highlightSelection() {
  document.querySelectorAll(".item-button.active, .pdf-link.active").forEach((element) => {
    element.classList.remove("active");
  });
  if (!state.selectedId) return;
  document.querySelectorAll(`[data-id="${CSS.escape(state.selectedId)}"]`).forEach((element) => {
    element.classList.add("active");
  });
}

function scrollWithin(container, element, center = false) {
  const containerBox = container.getBoundingClientRect();
  const elementBox = element.getBoundingClientRect();
  if (center) {
    container.scrollTop += elementBox.top - containerBox.top
      - (container.clientHeight - elementBox.height) / 2;
    return;
  }
  if (elementBox.top < containerBox.top) {
    container.scrollTop += elementBox.top - containerBox.top;
  } else if (elementBox.bottom > containerBox.bottom) {
    container.scrollTop += elementBox.bottom - containerBox.bottom;
  }
}

function selectItem(id, { scrollPdf = true, updateUrl = true } = {}) {
  const item = itemById(id);
  if (!item) return;
  state.selectedId = id;
  state.declarationIndex = 0;
  renderItemNav();
  renderItem(item);
  highlightSelection();

  const navButton = itemNav.querySelector(`[data-id="${CSS.escape(id)}"]`);
  if (navButton) scrollWithin(itemNav, navButton);
  const pdfTarget = state.linkById.get(id);
  if (scrollPdf && pdfTarget) {
    scrollWithin(pdfScroll, pdfTarget.marker, true);
  }
  if (updateUrl) updateHash();
}

function contentWidth(element) {
  const style = getComputedStyle(element);
  return Math.max(
    240,
    element.clientWidth - parseFloat(style.paddingLeft) - parseFloat(style.paddingRight),
  );
}

function fittedViewport(page) {
  const base = page.getViewport({ scale: 1 });
  const scale = Math.min(MAX_RENDER_SCALE, contentWidth(pdfScroll) / base.width);
  return page.getViewport({ scale });
}

function annotationBox(annotation, viewport) {
  const converted = viewport.convertToViewportRectangle(annotation.rect);
  return {
    left: Math.min(converted[0], converted[2]),
    top: Math.min(converted[1], converted[3]),
    width: Math.abs(converted[2] - converted[0]),
    height: Math.abs(converted[3] - converted[1]),
  };
}

async function renderPdf(token) {
  if (!state.pdf || token !== state.renderToken) return;
  pdfScroll.innerHTML = "";
  state.linkById.clear();

  for (let pageNumber = 1; pageNumber <= state.pdf.numPages; pageNumber += 1) {
    if (token !== state.renderToken) return;
    pdfStatus.textContent = `Rendering ${pageNumber}/${state.pdf.numPages}`;
    const page = await state.pdf.getPage(pageNumber);
    const viewport = fittedViewport(page);
    const outputScale = Math.min(window.devicePixelRatio || 1, 2);
    const pageElement = document.createElement("div");
    pageElement.className = "pdf-page";
    pageElement.dataset.page = String(pageNumber);
    pageElement.style.width = `${viewport.width}px`;
    pageElement.style.height = `${viewport.height}px`;

    const canvas = document.createElement("canvas");
    canvas.width = Math.floor(viewport.width * outputScale);
    canvas.height = Math.floor(viewport.height * outputScale);
    canvas.style.width = `${viewport.width}px`;
    canvas.style.height = `${viewport.height}px`;
    const context = canvas.getContext("2d", { alpha: false });
    pageElement.appendChild(canvas);

    const pageLabel = document.createElement("span");
    pageLabel.className = "page-number";
    pageLabel.textContent = String(pageNumber);
    pageElement.appendChild(pageLabel);
    pdfScroll.appendChild(pageElement);

    await page.render({
      canvasContext: context,
      viewport,
      transform: outputScale === 1 ? null : [outputScale, 0, 0, outputScale, 0, 0],
    }).promise;

    const annotations = await page.getAnnotations({ intent: "display" });
    for (const annotation of annotations) {
      const id = normalizeDestination(annotation.dest);
      if (!id || !itemById(id) || !annotation.rect) continue;
      const box = annotationBox(annotation, viewport);
      const marker = document.createElement("button");
      marker.type = "button";
      marker.className = "pdf-link";
      marker.dataset.id = id;
      marker.title = `Show Lean for ${itemById(id).number}`;
      marker.style.left = `${box.left}px`;
      marker.style.top = `${box.top}px`;
      marker.style.width = `${Math.max(26, box.width)}px`;
      marker.style.height = `${Math.max(17, box.height)}px`;
      marker.addEventListener("click", (event) => {
        event.preventDefault();
        event.stopPropagation();
        selectItem(id, { scrollPdf: false });
      });
      pageElement.appendChild(marker);
      if (!state.linkById.has(id)) {
        state.linkById.set(id, { page: pageElement, marker });
      }
    }
  }

  const markerCount = state.linkById.size;
  const expected = state.chapterData.items.length;
  pdfStatus.textContent = `${state.pdf.numPages} pages · ${markerCount}/${expected} markers`;
  if (markerCount !== expected) {
    showToast(`Marker audit: expected ${expected}, found ${markerCount}`);
  }
  highlightSelection();
  const selected = state.linkById.get(state.selectedId);
  if (selected) scrollWithin(pdfScroll, selected.marker, true);
}

async function loadChapter(chapterNumber, requestedItem = "") {
  const chapterMeta = state.manifest.chapters.find((chapter) => chapter.number === chapterNumber)
    || state.manifest.chapters[0];
  const token = ++state.renderToken;
  state.chapterMeta = chapterMeta;
  state.selectedId = "";
  state.declarationIndex = 0;
  state.linkById.clear();
  itemSearch.value = "";
  state.query = "";
  chapterSelect.value = String(chapterMeta.number);
  pdfStatus.textContent = "Loading";
  setLoading("Loading chapter data");

  try {
    if (state.pdf) {
      await state.pdf.destroy();
      state.pdf = null;
    }
    const response = await fetch(chapterMeta.data, { cache: "no-store" });
    if (!response.ok) throw new Error(`Unable to load ${chapterMeta.data}: ${response.status}`);
    const chapterData = await response.json();
    if (token !== state.renderToken) return;
    state.chapterData = chapterData;
    renderItemNav();
    const initialItem = itemById(requestedItem) || chapterData.items[0];
    if (initialItem) selectItem(initialItem.id, { scrollPdf: false, updateUrl: true });

    setLoading("Rendering TeX companion");
    state.pdf = await pdfjsLib.getDocument(chapterMeta.pdf).promise;
    if (token !== state.renderToken) return;
    await renderPdf(token);
  } catch (error) {
    if (token === state.renderToken) showError(error);
  }
}

function populateChapterSelect() {
  chapterSelect.innerHTML = "";
  for (const chapter of state.manifest.chapters) {
    const option = document.createElement("option");
    option.value = String(chapter.number);
    option.textContent = `${chapter.number} · ${chapter.title.replace(/^Chapter\s+\d+\s*[:.-]?\s*/i, "")}`;
    chapterSelect.appendChild(option);
  }
}

function applySplitPercent(value) {
  const clamped = Math.min(74, Math.max(38, value));
  document.documentElement.style.setProperty("--source-size", `${clamped}%`);
  return clamped;
}

function splitFromPointer(event) {
  const bounds = workspace.getBoundingClientRect();
  return ((event.clientX - bounds.left) / bounds.width) * 100;
}

function schedulePdfRender() {
  if (!state.pdf) return;
  clearTimeout(state.resizeTimer);
  state.resizeTimer = window.setTimeout(() => {
    const token = ++state.renderToken;
    renderPdf(token).catch(showError);
  }, 180);
}

function setupSplitter() {
  const savedValue = localStorage.getItem(SPLIT_STORAGE_KEY);
  const saved = Number(savedValue);
  if (savedValue !== null && Number.isFinite(saved)) applySplitPercent(saved);

  splitter.addEventListener("pointerdown", (event) => {
    if (window.matchMedia("(max-width: 820px)").matches) return;
    state.dragging = true;
    splitter.setPointerCapture(event.pointerId);
    workspace.classList.add("resizing");
    applySplitPercent(splitFromPointer(event));
  });
  splitter.addEventListener("pointermove", (event) => {
    if (!state.dragging) return;
    applySplitPercent(splitFromPointer(event));
  });
  const finish = (event) => {
    if (!state.dragging) return;
    state.dragging = false;
    if (splitter.hasPointerCapture(event.pointerId)) splitter.releasePointerCapture(event.pointerId);
    workspace.classList.remove("resizing");
    const split = applySplitPercent(splitFromPointer(event));
    localStorage.setItem(SPLIT_STORAGE_KEY, String(split));
    schedulePdfRender();
  };
  splitter.addEventListener("pointerup", finish);
  splitter.addEventListener("pointercancel", finish);
  splitter.addEventListener("keydown", (event) => {
    if (!["ArrowLeft", "ArrowRight", "Home", "End"].includes(event.key)) return;
    event.preventDefault();
    const current = Number.parseFloat(
      getComputedStyle(document.documentElement).getPropertyValue("--source-size"),
    ) || 59;
    const next = event.key === "Home"
      ? 40
      : event.key === "End"
        ? 72
        : current + (event.key === "ArrowLeft" ? -3 : 3);
    const split = applySplitPercent(next);
    localStorage.setItem(SPLIT_STORAGE_KEY, String(split));
    schedulePdfRender();
  });
}

async function initialize() {
  try {
    const response = await fetch("data/manifest.json", { cache: "no-store" });
    if (!response.ok) throw new Error(`Unable to load reader manifest: ${response.status}`);
    state.manifest = await response.json();
    repositoryLink.href = state.manifest.repository;
    buildMeta.textContent = `${state.manifest.leanToolchain} · ${state.manifest.commit}`;
    buildMeta.title = buildMeta.textContent;
    populateChapterSelect();
    setupSplitter();
    const requested = hashState();
    await loadChapter(requested.chapter || state.manifest.chapters[0].number, requested.item);
  } catch (error) {
    showError(error);
  }
}

itemNav.addEventListener("click", (event) => {
  const button = event.target.closest(".item-button");
  if (button) selectItem(button.dataset.id);
});

itemSearch.addEventListener("input", (event) => {
  state.query = event.target.value;
  renderItemNav();
  highlightSelection();
});

chapterSelect.addEventListener("change", () => {
  loadChapter(Number(chapterSelect.value));
});

declarationSelect.addEventListener("change", () => {
  state.declarationIndex = Number(declarationSelect.value);
  renderDeclaration();
});

copyCode.addEventListener("click", async () => {
  const item = itemById(state.selectedId);
  const declaration = item?.declarations[state.declarationIndex];
  if (!declaration) return;
  try {
    await navigator.clipboard.writeText(declaration.code);
    showToast("Lean code copied");
  } catch {
    showToast("Clipboard access was denied");
  }
});

window.addEventListener("hashchange", () => {
  const requested = hashState();
  if (!requested.chapter || !state.manifest) return;
  if (requested.chapter !== state.chapterMeta?.number) {
    loadChapter(requested.chapter, requested.item);
  } else if (requested.item && requested.item !== state.selectedId) {
    selectItem(requested.item, { updateUrl: false });
  }
});

const resizeObserver = new ResizeObserver(() => schedulePdfRender());
resizeObserver.observe(pdfScroll);

initialize();
