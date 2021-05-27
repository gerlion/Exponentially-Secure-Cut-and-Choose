# A Novel Proof of Shuffle
The Coq code comes with makefiles 
# Dependencies 
The Coq Proof Assistant, version 8.8.2
OCaml, version 4.03.0
coq-color
# Installation instructions
(These instructions were tested on a clean Ubuntu-18.04.4 (64 bit) install inside VirtualBox)
## Installing opam 2
sudo add-apt-repository ppa:avsm/ppa
sudo apt update
sudo apt install opam
## Init opam
sudo apt-get install m4
sudo apt install libgmp-dev
opam init --comp 4.03.0
eval $(opam env)
opam update
## Install coq
opam pin add coq 8.8.2
opam repo add coq-released https://coq.inria.fr/opam/released
opam update
opam install coq-color
# Coq code
Running make newProofOfShuffle.vo.vo will prompt Coq to check the proofs
### Related Paper
This code is from "A Novel Proof of Shuffle: Exponentially Secure Cut-and-Choose"
by Thomas Haines and Johannes Mueller https://eprint.iacr.org/2021/588
