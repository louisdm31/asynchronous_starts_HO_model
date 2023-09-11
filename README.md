This repository contains the formal proof validating the results of our publication "Synchronization modulo k in Dynamic Networks".
The whole paper can be found at [ref](https://link.springer.com/chapter/10.1007/978-3-030-91081-5_28).
The proof, written using the Isabelle proof assistant, is structured as follows:

- The [HOModel](./HOModel.thy) file contains the basic primitives of our computational model.
- The [SynchMod](SynchMod.thy) file contains the definition of our algorithm.
- The [SynchModProof](SynchModProof.thy) file contains the proof or both safety and liveness properties.
- As the formal definitions in [SynchMod](SynchMod.thy) are, at first glance, quite different from 
the pseudo-code of the paper, we also provide [PseudoCodeEquiv](PseudoCodeEquiv.thy), which
proves the equivalence between both of them.
