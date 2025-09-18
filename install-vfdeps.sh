if [ ! -L "/tmp/vf-llvm-clang-build-$VF_LLVM_CLANG_BUILD_VERSION" ]; then
    ln -sf /vf-llvm-clang-build-$VF_LLVM_CLANG_BUILD_VERSION /tmp/vf-llvm-clang-build-$VF_LLVM_CLANG_BUILD_VERSION
fi
if [ ! -L "/tmp/$VFDEPS_NAME" ]; then
    ln -sf /$VFDEPS_NAME /tmp/$VFDEPS_NAME
fi