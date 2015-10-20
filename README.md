# Principia Metaphysica: Formalization


Contributors
-----------------------

* [Christoph Benzmüller](http://christoph-benzmueller.de/)
* [Edward Zalta](https://mally.stanford.edu/zalta.html)

Outline
-----------------------

This repository contains a computer-assisted formalization of Ed
Zalta's Principia Metaphysica, which is based on Zalta's Theory of
Abstract Objects. This work is based on a second-order modal logic
which employs 
relational type theory as a foundation.

The formalization is carried out in classical higher-order logic (HOL)
employing Benzmüller approach to embed non-classical logics in
HOL. This enables the use of the proof assistants, theorem
provers and model finders such as:

* [Isabelle/HOL](https://isabelle.in.tum.de/)
* [LEO-II](http://page.mi.fu-berlin.de/cbenzmueller/leo/) 
* [Satallax](https://mathgate.info/cebrown/satallax/)
* [Nitpick](http://www4.in.tum.de/~blanchet/nitpick.html)



Main Challenges
-----------------------

* Bridging between the relational foundation of Zalta's theory of
abstract objects and the functional foundation of HOL

* Controlling comprehension; full comprehension (as given in HOL) is too strong

* Combining static evaluation of certain language constructs (e.g. actuality and
  definite description) wrt to a fixed current world with a dynamic
  evaluation of the other language constructs wrt to the possible world
  under consideration


