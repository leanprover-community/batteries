import { DeclarationDataCenter } from "./declaration-data.js";

annotateInstances();
annotateInstancesFor()

async function annotateInstances() {
  const dataCenter = await DeclarationDataCenter.init();
  const instanceForLists = [...(document.querySelectorAll(".instances-list"))];

  for (const instanceForList of instanceForLists) {
    const className = instanceForList.id.slice("instances-list-".length);
    const instances = dataCenter.instancesForClass(className);
    var innerHTML = "";
    for(var instance of instances) {
      const instanceLink = dataCenter.declNameToLink(instance);
      innerHTML += `<li><a href="${SITE_ROOT}${instanceLink}">${instance}</a></li>`
    }
    instanceForList.innerHTML = innerHTML;
  }
}

async function annotateInstancesFor() {
  const dataCenter = await DeclarationDataCenter.init();
  const instanceForLists = [...(document.querySelectorAll(".instances-for-list"))];

  for (const instanceForList of instanceForLists) {
    const typeName = instanceForList.id.slice("instances-for-list-".length);
    const instances = dataCenter.instancesForType(typeName);

    if (instances.length == 0) {
      instanceForList.remove();
    } else {
      var innerHTML = "";
      for(var instance of instances) {
        const instanceLink = dataCenter.declNameToLink(instance);
        innerHTML += `<li><a href="${SITE_ROOT}${instanceLink}">${instance}</a></li>`;
      }
      const instanceEnum = instanceForList.querySelector(".instances-for-enum");
      instanceEnum.innerHTML = innerHTML;
    }
  }
}
