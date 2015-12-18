Require Import Fin.

Parameters 
(entropy  : Set)
(draw_fin : entropy -> forall n, Fin.t n).

Axiom draw_fin_correct : forall n m, exists e, draw_fin e n = m.