#!/bin/zsh
cd -- "${0:A:h}" || exit 1
print -r -- "加拿大死亡之路 · Mac 汉化 20261015"
args=(restore)
if (( $# )); then args+=(--app "$1"); fi
./工具/installer "${args[@]}"
result=$?
if [[ -t 0 ]]; then print ""; read -k 1 "?按任意键关闭……"; print ""; fi
exit "$result"
