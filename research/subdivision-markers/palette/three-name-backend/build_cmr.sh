#!/usr/bin/env bash
# Run on a disposable, pinned sparse checkout under the caller's resource limits.
set -eu
cd "${1:?provide the discopt/cmr checkout path}"
test "$(git rev-parse HEAD)" = 0c42a44deb8262a1f2a400add5d6be80e90eda3c
mkdir -p local/cmr
cat > local/cmr/config.h <<'EOF'
#define CMR_CMAKE_BUILD_TYPE "Release"
#define CMR_VERSION_MAJOR 1
#define CMR_VERSION_MINOR 4
#define CMR_VERSION_PATCH 0
#define CMR_WITH_GMP 0
EOF
echo '#define CMR_EXPORT' > local/cmr/export.h
mapfile -t files < <(sed -n '/^add_library(cmr$/,/^)/p' CMakeLists.txt | sed -n 's/^  \(src\/cmr\/.*\.c\)$/\1/p')
test "${#files[@]}" -gt 1
cc -std=gnu99 -O1 -DNDEBUG -ffunction-sections -fdata-sections -Wl,--gc-sections -Iinclude -Ilocal -Isrc/cmr src/main/graphic_main.c "${files[@]}" -lm -o local/cmr-graphic
sha256sum local/cmr-graphic
