/**
 * This module is a wrapper that facilitates manipulating the declaration data.
 *
 * Please see {@link DeclarationDataCenter} for more information.
 */

const CACHE_DB_NAME = "declaration-data";
const CACHE_DB_VERSION = 1;
const CACHE_DB_KEY = "DECLARATIONS_KEY";

/**
 * The DeclarationDataCenter is used for declaration searching.
 *
 * For usage, see the {@link init} and {@link search} methods.
 */
export class DeclarationDataCenter {
  /**
   * The declaration data. Users should not interact directly with this field.
   *
   * *NOTE:* This is not made private to support legacy browsers.
   */
  declarationData = null;

  /**
   * Used to implement the singleton, in case we need to fetch data mutiple times in the same page.
   */
  static requestSingleton = null;

  /**
   * Construct a DeclarationDataCenter with given data.
   *
   * Please use {@link DeclarationDataCenter.init} instead, which automates the data fetching process.
   * @param {*} declarationData
   */
  constructor(declarationData) {
    this.declarationData = declarationData;
  }

  /**
   * The actual constructor of DeclarationDataCenter
   * @returns {Promise<DeclarationDataCenter>}
   */
  static async init() {
    if (DeclarationDataCenter.requestSingleton === null) {
      DeclarationDataCenter.requestSingleton = DeclarationDataCenter.getData();
    }
    return await DeclarationDataCenter.requestSingleton;
  }

  static async getData() {
    const dataListUrl = new URL(
      `${SITE_ROOT}/declarations/declaration-data.bmp`,
      window.location
    );

    // try to use cache first
    // TODO: This API is not thought 100% through. If we have a DB cached
    // already it will not even ask the remote for a new one so we end up
    // with outdated declaration-data. This has to have some form of cache
    // invalidation: https://github.com/leanprover/doc-gen4/issues/133
    // const data = await fetchCachedDeclarationData().catch(_e => null);
    const data = null;
    if (data) {
      // if data is defined, use the cached one.
      return new DeclarationDataCenter(data);
    } else {
      // undefined. then fetch the data from the server.
      const dataListRes = await fetch(dataListUrl);
      const data = await dataListRes.json();
      // TODO https://github.com/leanprover/doc-gen4/issues/133
      // await cacheDeclarationData(data);
      return new DeclarationDataCenter(data);
    }
  }

  /**
   * Search for a declaration.
   * @returns {Array<any>}
   */
  search(pattern, strict = true, allowedKinds = undefined, maxResults = undefined) {
    if (!pattern) {
      return [];
    }
    if (strict) {
      let decl = this.declarationData.declarations[pattern];
      return decl ? [decl] : [];
    } else {
      return getMatches(this.declarationData.declarations, pattern, allowedKinds, maxResults);
    }
  }

  /**
   * Search for all instances of a certain typeclass
   * @returns {Array<String>}
   */
  instancesForClass(className) {
    const instances = this.declarationData.instances[className];
    if (!instances) {
      return [];
    } else {
      return instances;
    }
  }

  /**
   * Search for all instances that involve a certain type
   * @returns {Array<String>}
   */
  instancesForType(typeName) {
    const instances = this.declarationData.instancesFor[typeName];
    if (!instances) {
      return [];
    } else {
      return instances;
    }
  }

  /**
   * Analogous to Lean declNameToLink
   * @returns {String}
   */
  declNameToLink(declName) {
    return this.declarationData.declarations[declName].docLink;
  }

  /**
   * Find all modules that imported the given one.
   * @returns {Array<String>}
   */
  moduleImportedBy(moduleName) {
    return this.declarationData.modules[moduleName].importedBy;
  }

  /**
   * Analogous to Lean moduleNameToLink
   * @returns {String}
   */
  moduleNameToLink(moduleName) {
    return this.declarationData.modules[moduleName].url;
  }
}

function isSeparator(char) {
  return char === "." || char === "_";
}

// HACK: the fuzzy matching is quite hacky

function matchCaseSensitive(declName, lowerDeclName, pattern) {
  let i = 0,
    j = 0,
    err = 0,
    lastMatch = 0;
  while (i < declName.length && j < pattern.length) {
    if (pattern[j] === declName[i] || pattern[j] === lowerDeclName[i]) {
      err += (isSeparator(pattern[j]) ? 0.125 : 1) * (i - lastMatch);
      if (pattern[j] !== declName[i]) err += 0.5;
      lastMatch = i + 1;
      j++;
    } else if (isSeparator(declName[i])) {
      err += 0.125 * (i + 1 - lastMatch);
      lastMatch = i + 1;
    }
    i++;
  }
  err += 0.125 * (declName.length - lastMatch);
  if (j === pattern.length) {
    return err;
  }
}

function getMatches(declarations, pattern, allowedKinds = undefined, maxResults = undefined) {
  const lowerPats = pattern.toLowerCase().split(/\s/g);
  const patNoSpaces = pattern.replace(/\s/g, "");
  const results = [];
  for (const [name, {
    kind,
    docLink,
  }] of Object.entries(declarations)) {
    // Apply "kind" filter
    if (allowedKinds !== undefined) {
      if (!allowedKinds.has(kind)) {
        continue;
      }
    }
    const lowerName = name.toLowerCase();
    let err = matchCaseSensitive(name, lowerName, patNoSpaces);
    if (err !== undefined) {
      results.push({
        name,
        kind,
        err,
        lowerName,
        docLink,
      });
    }
  }
  return results.sort(({ err: a }, { err: b }) => a - b).slice(0, maxResults);
}

// TODO: refactor the indexedDB part to be more robust

/**
 * Get the indexedDB database, automatically initialized.
 * @returns {Promise<IDBDatabase>}
 */
async function getDeclarationDatabase() {
  return new Promise((resolve, reject) => {
    const request = indexedDB.open(CACHE_DB_NAME, CACHE_DB_VERSION);

    request.onerror = function (event) {
      reject(
        new Error(
          `fail to open indexedDB ${CACHE_DB_NAME} of version ${CACHE_DB_VERSION}`
        )
      );
    };
    request.onupgradeneeded = function (event) {
      let db = event.target.result;
      // We only need to store one object, so no key path or increment is needed.
      db.createObjectStore("declaration");
    };
    request.onsuccess = function (event) {
      resolve(event.target.result);
    };
  });
}

/**
 * Store data in indexedDB object store.
 * @param {Map<string, any>} data
 */
async function cacheDeclarationData(data) {
  let db = await getDeclarationDatabase();
  let store = db
    .transaction("declaration", "readwrite")
    .objectStore("declaration");
  return new Promise((resolve, reject) => {
    let clearRequest = store.clear();
    let addRequest = store.add(data, CACHE_DB_KEY);

    addRequest.onsuccess = function (event) {
      resolve();
    };
    addRequest.onerror = function (event) {
      reject(new Error(`fail to store declaration data`));
    };
    clearRequest.onerror = function (event) {
      reject(new Error("fail to clear object store"));
    };
  });
}

/**
 * Retrieve data from indexedDB database.
 * @returns {Promise<Map<string, any>|undefined>}
 */
async function fetchCachedDeclarationData() {
  let db = await getDeclarationDatabase();
  let store = db
    .transaction("declaration", "readonly")
    .objectStore("declaration");
  return new Promise((resolve, reject) => {
    let transactionRequest = store.get(CACHE_DB_KEY);
    transactionRequest.onsuccess = function (event) {
      resolve(event.target.result);
    };
    transactionRequest.onerror = function (event) {
      reject(new Error(`fail to store declaration data`));
    };
  });
}
