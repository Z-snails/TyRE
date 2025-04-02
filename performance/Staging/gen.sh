#!/bin/sh

idris2 --find-ipkg Staging/ILex.idr --exec main > Staging/ILexGenerated.idr
