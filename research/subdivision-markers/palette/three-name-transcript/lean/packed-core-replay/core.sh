#!/bin/bash
set -eu
cd "$(dirname "$0")"
python replay.py core 73c18aff095ccfe11bb60bfd3c7097fca033fbb5 PACKED-CORE-SOURCES.sha256 e73c795ee4e0b6a5f194bf9e879fd24cccbbd0a0fab88ca84d71d85d9c60d4b8 packed-producer 396600d0b56f71072f9f1ac5da1091bf36fc058097db0507d3343f33430b6f58
