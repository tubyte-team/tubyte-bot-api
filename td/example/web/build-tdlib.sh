#!/bin/sh
cd $(dirname $0)

emcmake true 2> /dev/null || { echo 'emcmake not found. Install emsdk and add emcmake and emmake to PATH environment variable. See instruction at https://kripken.github.io/emscripten-site/docs/getting_started/downloads.html. Do not forget to add `emcmake` and `emmake` to the PATH environment variable via `emsdk/emsdk_env.sh` script.'; exit 1; }

rm -rf build/generate
rm -rf build/asmjs
rm -rf build/wasm

mkdir -p build/generate
mkdir -p build/asmjs
mkdir -p build/wasm

TD_ROOT=$(realpath ../../)
OPENSSL_ROOT=$(realpath ./build/crypto/)
OPENSSL_CRYPTO_LIBRARY=$OPENSSL_ROOT/lib/libcrypto.a
OPENSSL_SSL_LIBRARY=$OPENSSL_ROOT/lib/libssl.a

OPENSSL_OPTIONS="-DOPENSSL_FOUND=1 \
  -DOPENSSL_ROOT_DIR=\"$OPENSSL_ROOT\" \
  -DOPENSSL_INCLUDE_DIR=\"$OPENSSL_ROOT/include\" \
  -DOPENSSL_CRYPTO_LIBRARY=\"$OPENSSL_CRYPTO_LIBRARY\" \
  -DOPENSSL_SSL_LIBRARY=\"$OPENSSL_SSL_LIBRARY\" \
  -DOPENSSL_LIBRARIES=\"$OPENSSL_SSL_LIBRARY;$OPENSSL_CRYPTO_LIBRARY\" \
  -DOPENSSL_VERSION=\"1.1.0l\""

cd build/generate
cmake $TD_ROOT || exit 1
cd ../..

cd build/wasm
eval emcmake cmake -DCMAKE_BUILD_TYPE=MinSizeRel $OPENSSL_OPTIONS $TD_ROOT || exit 1
cd ../..

cd build/asmjs
eval emcmake cmake -DCMAKE_BUILD_TYPE=MinSizeRel $OPENSSL_OPTIONS -DASMJS=1 $TD_ROOT || exit 1
cd ../..

echo "Generating TDLib autogenerated source files..."
cmake --build build/generate --target prepare_cross_compiling || exit 1
echo "Building TDLib to WebAssembly..."
cmake --build build/wasm --target td_wasm || exit 1
echo "Building TDLib to asm.js..."
cmake --build build/asmjs --target td_asmjs || exit 1
