#!/bin/bash
for n in *.nb; do
    echo $n;
    sed -i '' -e "s/PDESymbolics2020/PDESymbolics2022/" $n;
done
