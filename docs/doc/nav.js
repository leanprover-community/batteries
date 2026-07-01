/**
 * This module is used to implement persistent navbar expansion.
 */

// The variable to store the expansion information.
let expanded = {};

// Load expansion information from sessionStorage.
for (const e of (sessionStorage.getItem("expanded") || "").split(",")) {
  if (e !== "") {
    expanded[e] = true;
  }
}

/**
 * Save expansion information to sessionStorage.
 */
function saveExpanded() {
  sessionStorage.setItem(
    "expanded",
    Object.getOwnPropertyNames(expanded)
      .filter((e) => expanded[e])
      .join(",")
  );
}

// save expansion information when user change the expansion.
for (const elem of document.getElementsByClassName("nav_sect")) {
  const id = elem.getAttribute("data-path");
  if (!id) continue;
  if (expanded[id]) {
    elem.open = true;
  }
  elem.addEventListener("toggle", () => {
    expanded[id] = elem.open;
    saveExpanded();
  });
}

// Scroll to center.
for (const currentFileLink of document.getElementsByClassName("visible")) {
  currentFileLink.scrollIntoView({ block: "center" });
}