#!/bin/bash

set -e -x

if [[ "$RUST_REPO_DIR" = "" ]]; then
  echo "Please point RUST_REPO_DIR to the root directory of a Rust repo"
  exit 1
fi

if ! git -C "$RUST_REPO_DIR" diff --quiet .; then
  echo "Your Rust repo working directory at RUST_REPO_DIR is dirty; please clean it first"
  exit 1
fi
if ! git -C "$RUST_REPO_DIR" diff --cached --quiet .; then
  echo "Your Rust repo index at RUST_REPO_DIR is dirty; please clean it first"
  exit 1
fi
RUST_ALLOC_DIR="$RUST_REPO_DIR/library/alloc/src"

pushd "$(dirname "$0")"

. ./update-target.sh

if ! git diff --quiet .; then
  echo "Your working copy is dirty; please clean it up first"
  exit 1
fi

. ./metadata.sh
mkdir -p update-repo
pushd update-repo
if [ ! -e .git ]; then
  git init
fi
if ! git diff --quiet .; then
  echo "Update repo working directory is dirty; please clean it up first"
  exit 1
fi
if ! git diff --cached --quiet .; then
  echo "Update repo index is dirty; please clean it up first"
  exit 1
fi
git checkout main || true
# TODO: Do some sanity checks here. For now, we assume
# this branch is either dangling (no commits), or is older than the base
# commit, or is at the base commit, or is at the target commit.
if [[ ! "$(git tag --points-at HEAD)" = "rust-$TARGET_RUST_COMMIT_SHA" ]]; then
  if [[ ! "$(git tag --points-at HEAD)" = "rust-$RUST_COMMIT_SHA" ]]; then
    git -C "$RUST_REPO_DIR" checkout $RUST_COMMIT_SHA
    git -C "$RUST_REPO_DIR" clean --interactive -x -d
    rm -Rf ../update-repo/*
    cp -R "$RUST_ALLOC_DIR"/* .
    git add .
    git commit -m "Rust commit $RUST_COMMIT_SHA"
    git tag rust-$RUST_COMMIT_SHA
  fi
  git -C "$RUST_REPO_DIR" checkout $TARGET_RUST_COMMIT_SHA
  rm -Rf ../update-repo/*
  cp -R "$RUST_ALLOC_DIR"/* .
  git add .
  git commit -m "Rust commit $TARGET_RUST_COMMIT_SHA"
  git tag rust-$TARGET_RUST_COMMIT_SHA
fi

git checkout rust-$RUST_COMMIT_SHA

if ! git checkout vf-original; then
  git checkout -b vf-original
  git -C ../original clean --interactive -x -d
  rm -Rf ../update-repo/*
  cp -R ../original/* .
  git add .
  git commit -m "vf-original-$RUST_COMMIT_SHA"
  git tag vf-original-$RUST_COMMIT_SHA
fi
if ! git checkout vf-original-$TARGET_RUST_COMMIT_SHA; then
  git reset --hard vf-original-$RUST_COMMIT_SHA
  git merge rust-$TARGET_RUST_COMMIT_SHA
  git tag vf-original-$TARGET_RUST_COMMIT_SHA
fi
git checkout vf-original-$RUST_COMMIT_SHA

if ! git checkout vf-with-directives; then
  git checkout -b vf-with-directives
  git -C ../with-directives clean --interactive -x -d
  rm -Rf ../update-repo/*
  cp -R ../with-directives/* .
  git add .
  git commit -m "vf-with-directives-$RUST_COMMIT_SHA"
  git tag vf-with-directives-$RUST_COMMIT_SHA
fi
if ! git checkout vf-with-directives-$TARGET_RUST_COMMIT_SHA; then
  git merge vf-original-$TARGET_RUST_COMMIT_SHA
  git tag vf-with-directives-$TARGET_RUST_COMMIT_SHA
fi
git checkout vf-with-directives-$RUST_COMMIT_SHA

if ! git checkout vf-verified; then
  git checkout -b vf-verified
  git -C ../verified clean --interactive -x -d
  rm -Rf ../update-repo/*
  cp -R ../verified/* .
  git add .
  git commit -m "vf-verified-$RUST_COMMIT_SHA"
  git tag vf-verified-$RUST_COMMIT_SHA
fi
if ! git checkout vf-verified-$TARGET_RUST_COMMIT_SHA; then
  git merge vf-with-directives-$TARGET_RUST_COMMIT_SHA
  git tag vf-verified-$TARGET_RUST_COMMIT_SHA
fi
