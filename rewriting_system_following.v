Require Import Vector
               rewriting_system.

Import VectorNotations.
Infix "++" := append.

Fixpoint fin_lift1 {n} (m : Fin.t n) := match m with
| Fin.F1 n   => @Fin.F1 (S n)
| Fin.FS _ m => Fin.FS (fin_lift1 m)
end.

Coercion fin_lift1 : Fin.t >-> Fin.t.


Class RW_FOLLOWING (Follower Followed : REWRITING_SYSTEM) :=
{
    semantics : (@configuration Follower) -> (@configuration Followed);

    correct :                                                             forall cr1 cr2,
        `(Follower) cr1 → cr2  ->  semantics cr1 = semantics cr2  \/  
                                   `(Followed) semantics cr1 → semantics cr2;

    complete :                                                        forall cd1 cd2 cr1,
        `(Followed) cd1 → cd2  ->  semantics cr1 = cd1 -> 
            exists n (crs : Vector.t configuration n) cr2,
            (**)Forall (fun cr => semantics cr = cd1) crs /\
            (**)semantics cr2 = cd2                       /\
            (**)forall m : Fin.t (n+1), 
                    (cr1 :: crs ++ [cr2])[@m] → (crs ++ [cr2])[@m];

    no_silent_loops :
      ~ exists crs : nat -> configuration, (*a stream of configurations*)
          forall n, 
          (**)  `(Follower) crs n  →  crs (S n)  /\ 
          (**)~ `(Followed) semantics (crs n)  →  semantics (crs (S n))
}.