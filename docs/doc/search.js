/**
 * This module is used to handle user's interaction with the search form.
 */

import { DeclarationDataCenter } from "./declaration-data.js";

// Search form and input in the upper right toolbar
const SEARCH_FORM = document.querySelector("#search_form");
const SEARCH_INPUT = SEARCH_FORM.querySelector("input[name=q]");

// Search form on the /search.html_page.  These may be null.
const SEARCH_PAGE_INPUT = document.querySelector("#search_page_query")
const SEARCH_RESULTS = document.querySelector("#search_results")

// Max results to show for autocomplete or /search.html page.
const AC_MAX_RESULTS = 30
const SEARCH_PAGE_MAX_RESULTS = undefined

// Search results are sorted into blocks for better performance; this determines the number of search results per block.
// Must be positive, may be infinite.
const RESULTS_PER_BLOCK = 50

// Create an `div#autocomplete_results` to hold all autocomplete results.
let ac_results = document.createElement("div");
ac_results.id = "autocomplete_results";
SEARCH_FORM.appendChild(ac_results);

/**
 * Attach `selected` class to the the selected autocomplete result.
 */
function handleSearchCursorUpDown(down) {
  const sel = ac_results.querySelector(`.selected`);
  const results = [...ac_results.getElementsByClassName("search_result")];
  const selIndex = results.indexOf(sel);
  let toSelect;
  if (sel) {
    sel.classList.remove("selected");
    toSelect = results[down ? selIndex + 1 : selIndex - 1];
  } else {
    toSelect = down ? results[0] : results[results.length-1];
  }
  if (toSelect){
    toSelect.classList.add("selected");
    toSelect.scrollIntoView({block:"nearest"});
  }
}

/**
 * Perform search (when enter is pressed).
 */
function handleSearchEnter() {
  const sel = ac_results.querySelector(`.selected .result_link a`) || document.querySelector(`#search_button`);
  sel.click();
}

/**
 * Allow user to navigate autocomplete results with up/down arrow keys, and choose with enter.
 */
SEARCH_INPUT.addEventListener("keydown", (ev) => {
  switch (ev.key) {
    case "Down":
    case "ArrowDown":
      ev.preventDefault();
      handleSearchCursorUpDown(true);
      break;
    case "Up":
    case "ArrowUp":
      ev.preventDefault();
      handleSearchCursorUpDown(false);
      break;
    case "Enter":
      ev.preventDefault();
      handleSearchEnter();
      break;
  }
});

/**
 * Remove all children of a DOM node.
 */
function removeAllChildren(node) {
  while (node.firstChild) {
    node.removeChild(node.lastChild);
  }
}

// counts how often `handleSearch` has already been called. Used to terminate the previous call whenever a new one has started.
var handleSearchCounter = 0;

/**
 * Handle user input and perform search.
 */
async function handleSearch(dataCenter, err, ev, sr, maxResults, autocomplete) {
  const text = ev.target.value;
  const callIndex = ++handleSearchCounter;

  // If no input clear all.
  if (!text) {
    sr.removeAttribute("state");
    removeAllChildren(sr);
    return;
  }

  // searching
  sr.setAttribute("state", "loading");

  if (dataCenter) {
    var allowedKinds;
    if (!autocomplete) {
      allowedKinds = new Set();
      document.querySelectorAll(".kind_checkbox").forEach((checkbox) =>
        {
          if (checkbox.checked) {
            allowedKinds.add(checkbox.value);
          }
        } 
      );
    }
    const result = dataCenter.search(text, false, allowedKinds, maxResults);

    // in case user has updated the input.
    if (ev.target.value != text) return;
  
    // update autocomplete results
    removeAllChildren(sr);
    for (let i = 0; i < result.length; i += RESULTS_PER_BLOCK) {
      // results are grouped into blocks, each block consisting of an inner block with `display: table`
      // and an outer block with `content-visibility: auto` that tells the browser to only render it
      // when it gets close to the viewport. These two wrappers can't be combined into a single element
      // because those two CSS properties are incompatible.
      const block = document.createElement("div");
      block.classList.add("search_result_block");
      const innerBlock = block.appendChild(document.createElement("div"));
      innerBlock.classList.add("search_result_block_inner");
      // put the next batch of results into the block, then insert the block into the DOM
      for (let j = i; j < Math.min(result.length, i + RESULTS_PER_BLOCK); j++){
        const row = innerBlock.appendChild(document.createElement("div"));
        row.classList.add("search_result");
        const linkdiv = row.appendChild(document.createElement("div"))
        linkdiv.classList.add("result_link");
        const link = linkdiv.appendChild(document.createElement("a"));
        link.innerText = result[j].name;
        link.title = result[j].name;
        link.href = SITE_ROOT + result[j].docLink;
      }
      sr.appendChild(block);
      // wait a moment before adding the next block, and only do so if this method hasn't been called since.
      await new Promise(resolve=>setTimeout(resolve,0));
      if (handleSearchCounter!=callIndex) return;
    }
  }
  // handle error
  else {
    removeAllChildren(sr);
    const d = sr.appendChild(document.createElement("a"));
    d.innerText = `Cannot fetch data, please check your network connection.\n${err}`;
  }
  sr.setAttribute("state", "done");
}

// https://www.joshwcomeau.com/snippets/javascript/debounce/
const debounce = (callback, wait) => {
  let timeoutId = null;
  return (...args) => {
    window.clearTimeout(timeoutId);
    timeoutId = window.setTimeout(() => {
      callback.apply(null, args);
    }, wait);
  };
}

// The debounce delay for the search. 90 ms is below the noticable input lag for me
const SEARCH_DEBOUNCE = 90;

DeclarationDataCenter.init()
  .then((dataCenter) => {
    // Search autocompletion.
    SEARCH_INPUT.addEventListener("input", debounce(ev => handleSearch(dataCenter, null, ev, ac_results, AC_MAX_RESULTS, true), SEARCH_DEBOUNCE));
    if(SEARCH_PAGE_INPUT) {
      SEARCH_PAGE_INPUT.addEventListener("input", ev => handleSearch(dataCenter, null, ev, SEARCH_RESULTS, SEARCH_PAGE_MAX_RESULTS, false))
      document.querySelectorAll(".kind_checkbox").forEach((checkbox) =>
        checkbox.addEventListener("input", ev => SEARCH_PAGE_INPUT.dispatchEvent(new Event("input")))
      );
      SEARCH_PAGE_INPUT.dispatchEvent(new Event("input"))
    };
    SEARCH_INPUT.dispatchEvent(new Event("input"))
  })
  .catch(e => {
    SEARCH_INPUT.addEventListener("input", debounce(ev => handleSearch(null, e, ev, ac_results, AC_MAX_RESULTS, true), SEARCH_DEBOUNCE));
    if(SEARCH_PAGE_INPUT) {
      SEARCH_PAGE_INPUT.addEventListener("input", ev => handleSearch(null, e, ev, SEARCH_RESULTS, SEARCH_PAGE_MAX_RESULTS, false));
    }
  });
