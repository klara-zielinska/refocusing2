Require Import Fin2
               Vector2
               rewriting_system.
        Import rewriting_system.Paths.



Local Open Scope vector.

Class RW_FOLLOWING                                    {configuration_er configuration_ed}
    (Follower : REWRITING_SYSTEM configuration_er)
    (Followed : REWRITING_SYSTEM configuration_ed) :=

{
    semantics : configuration_er -> configuration_ed;

    semantics_surj : forall cd, exists cr, semantics cr = cd;

    correct :                                                             forall cr1 cr2,
        `(Follower) cr1 → cr2  ->  semantics cr1 = semantics cr2  \/
                                   `(Followed) semantics cr1 → semantics cr2;

    complete :                                                        forall cd1 cd2 cr1,
        `(Followed) cd1 → cd2  ->  semantics cr1 = cd1 ->
            exists n (crs : Vector.t configuration_er n) cr2,
            (**)Forall (fun cr => semantics cr = cd1) crs /\
            (**)semantics cr2 = cd2                       /\
            (**)path (cr1 :: crs ++ [cr2]);

    no_silent_loops :
      ~ exists crs : nat -> configuration_er, (*a stream of configurations*)
          forall n,
          (**)  `(Follower) crs n  →  crs (S n)  /\
          (**)~ `(Followed) semantics (crs n)  →  semantics (crs (S n))
}.
