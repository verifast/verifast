// Used by the GitHub Actions CI workflow at .github/workflows/build.yml

module.exports = async ({github, context, core, assetPath, assetName, assetsToDeleteRegex, tag}) => {
  const owner = context.repo.owner;
  const repo = context.repo.repo;
  const fs = require('fs').promises;
  console.log("Getting release id for tag '%s'...", tag);
  const release = await github.rest.repos.getReleaseByTag({
    owner,
    repo,
    tag
  });
  const release_id = release.data.id;
  console.log("Retrieving list of assets for release id %s...", release_id);
  const assets = await github.rest.repos.listReleaseAssets({
    owner,
    repo,
    release_id
  });
  const data = await fs.readFile(assetPath);
  console.log("Uploading asset %s from %s...", assetName, assetPath);
  const uploadResponse = await github.rest.repos.uploadReleaseAsset({
    owner: context.repo.owner,
    repo: context.repo.repo,
    release_id: release.data.id,
    name: assetName,
    data
  });
  console.log("Upload response status: %s", uploadResponse.status);
  for (const asset of assets.data) {
    if (assetsToDeleteRegex.test(asset.name) && asset.name != assetName) {
      console.log("Deleting old asset %s...", asset.name);
      const deleteResponse = await github.rest.repos.deleteReleaseAsset({
        owner,
        repo,
        asset_id: asset.id
      });
      console.log("Delete response status: %s", deleteResponse.status);
    }
  }
};
