Require Import no_es_cl_ecca.
Require Import abstract_machine_facts.


Module Sim := DetAbstractMachine_Sim ECCa_es_cl_EAM_minus.

Import ECCa_es_cl_EAM_minus.
Import no_es_cl_ECCa.
Import no_es_cl_ECCa_Ref.R.



Let t1 := Lam0 (App0 (Lam0 (Lam0 (Var0 1))) (Var0 0)).


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


Let add_term0 := 
    Lam0 (Lam0 (Lam0 (Lam0 
        (App0 (App0 (Var0 3) 
            (Var0 1)) 
            (App0 (App0 (Var0 2) (Var0 1)) (Var0 0)))))).

Let mul_term0 := 
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

