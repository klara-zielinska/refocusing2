Require Import lam_cl_es_no.
Require Import abstract_machine_facts.




Module Sim := DetAbstractMachine_Sim Lam_ClES_NO_EAM_minus.

Import Lam_ClES_NO_EAM_minus.
Import Lam_ClES_NO_RefLang Lam_ClES_NO_Cal.RedLang.



Example t1 := Lam0 (App0 (Lam0 (Lam0 (Var0 1))) (Var0 0)).


Eval compute in 
    Sim.n_steps 
    ( c_init t1 )
    14.


Eval compute in 
    Sim.n_steps 
    ( c_init (Lam0 (App0  t1  (Var0 0) )) )
    20.



Fixpoint nat_term0 n :=
    match n with
    | 0   => Lam0 (Lam0 (Var0 0))
    | S n => Lam0 (Lam0 (App0 (Var0 1) (App0 (App0 (nat_term0 n) (Var0 1)) (Var0 0))))
    end.


Definition add_term0 := 
    Lam0 (Lam0 (Lam0 (Lam0 
        (App0 (App0 (Var0 3) 
            (Var0 1)) 
            (App0 (App0 (Var0 2) (Var0 1)) (Var0 0)))))).

Definition mul_term0 := 
    Lam0 (Lam0 (Lam0 (Lam0
        (App0 (App0

        (App0 (App0 (Var0 2) 
            (Lam0 (App0 (App0 add_term0 (Var0 4)) (Var0 0)) ))
            (nat_term0 0))

        (Var0 1)) (Var0 0))))).


Eval compute in
    Sim.n_steps 
    ( c_init (App0 (App0 mul_term0 (nat_term0 3)) (nat_term0 4)) ) 
    672.

