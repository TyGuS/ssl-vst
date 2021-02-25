# VST Tactics for SSL
Coq Tactics for the VST framework to support certified program synthesis using SuSLik.

## Requirements
- Coq (>= "8.10.0" & < "8.12~")
- Mathematical Components `ssreflect` (>= "1.10.0" & < "1.12~")
- Coq-Vst (>= "2.6" & < "2.7")
- CompCert Version 3.7 (you need to have the clightgen binary on your path, but where it lives doesn't matter)

## Installing
We recommend installing with OPAM:
```
opam repo add coq-released https://coq.inria.fr/opam/released
opam pin add coq-ssl-vst git+https://github.com/TyGuS/ssl-vst\#master --no-action --yes
opam install coq coq-mathcomp-ssreflect coq-ssl-vst coq-vst
```
## Building Examples
Simply change directory to the examples folder and run `make` to build all the examples.

