cabal build
cabal run -v0 cpsa4dl ./query.scm > ./query.pl
swipl -g "['./tst/yahalom.pl', './query.pl', './doc/cpsa4prolog.pl'], query." -t halt

