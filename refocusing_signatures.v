Require Export refocusing_lang.
Require Import Program.


Module Type RED_SEM (R : RED_LANG).

  Import R.

  Parameter dec : term -> forall {k1 k2}, context k1 k2 -> decomp k1 -> Prop.

  (** A redex in context will only ever be reduced to itself *)
  Axiom dec_redex_self : forall {k2} (r : redex k2) {k1} (c : context k1 k2), 
                             dec r c (d_red r c).

  Axiom decompose : forall (t : term) k1, ~ dead_ckind k1 ->
      (exists (v : value k1), t = v) \/
      (exists k2 (r : redex k2) (c : context k1 k2), t = c[r]).

  (** dec is left inverse of plug *)
  Axiom dec_correct  : forall {t k1 k2} {c : context k1 k2} {d}, 
                           dec t c d -> c[t] = d.

  Axiom dec_plug     : forall {k1 k2} (c : context k1 k2) {k3} {c0 : context k3 k1} {t d}, 
                           ~ dead_ckind k2 -> dec c[t] c0 d -> 
                           dec t (c ~+ c0) d.

  Axiom dec_plug_rev : forall {k1 k2} (c : context k1 k2) {k3} {c0 : context k3 k1} {t d}, 
                           ~ dead_ckind k2 ->  dec t (c ~+ c0) d -> 
                           dec c[t] c0 d.


  Inductive decempty : term -> forall {k}, decomp k -> Prop :=
  | d_intro : forall {t k} {d : decomp k}, dec t [_] d -> decempty t d.

  Inductive iter : forall {k}, decomp k -> value k -> Prop :=
  | i_val : forall {k} (v : value k), iter (d_val v) v
  | i_red : forall {k2} (r : redex k2) {t k1} (c : context k1 k2) {d v},
                contract r = Some t -> decempty c[t] d -> iter d v ->
                iter (d_red r c) v.

  Inductive eval : term -> value init_ckind -> Prop :=
  | e_intro : forall {t} {d : decomp init_ckind} {v : value init_ckind}, 
                  decempty t d -> iter d v -> eval t v.

End RED_SEM.



Module Type RED_REF_SEM (R : RED_LANG).

  Import R. 

  (** Functions specifying atomic steps of induction on terms and contexts -- needed to avoid explicit induction on terms and contexts in construction of the AM *)
  Parameter dec_term    : term -> forall k, interm_dec k.
  Parameter dec_context : forall ec k, value (k+>ec) -> interm_dec k.


  Axiom dec_term_correct : 
      forall t k, match dec_term t k with
      | in_red r       => t = r
      | in_val v       => t = v
      | in_term t0 ec0 => t = ec0:[t0]
      | in_dead        => dead_ckind k
      end.

  Axiom dec_context_correct : 
      forall ec k v, match dec_context ec k v with
      | in_red r      => ec:[v] = r
      | in_val v0     => ec:[v] = v0
      | in_term t ec0 => ec:[v] = ec0:[t]
      | in_dead       => dead_ckind (k+>ec) 
      end.


  Axiom dec_term_next_alive : 
      forall t k {t0 ec0}, dec_term t k = in_term t0 ec0 -> ~ dead_ckind (k+>ec0).

  Axiom dec_term_from_dead : 
      forall t k, dead_ckind k -> dec_term t k = in_dead k.

  Axiom dec_context_from_dead : 
      forall ec k (v : value (k+>ec)), 
          dead_ckind (k+>ec) -> dec_context ec k v = in_dead k.

  (** A decomposition function specified in terms of the atomic functions above *)
  Inductive dec : term -> forall {k1 k2}, context k1 k2 -> decomp k1 -> Prop :=
  | d_dec  : forall t {k1 k2} (c : context k1 k2) {r},
               dec_term t k2 = in_red r -> 
               dec t c (d_red r c)
  | d_v    : forall t {k1 k2} {c : context k1 k2} {v d},
               dec_term t k2 = in_val v ->
               decctx v c d ->
               dec t c d
  | d_term : forall t {t0 k1 k2} {c : context k1 k2} {ec d},
               dec_term t k2 = in_term t0 ec ->
               dec t0 (ec=:c) d ->
               dec t c d

  with decctx : forall {k2}, value k2 -> forall {k1}, context k1 k2 -> decomp k1 -> Prop :=
  | dc_end  : forall {k} (v : value k), 
                ~ dead_ckind k ->
                decctx v [_] (d_val v)
  | dc_dec  : forall ec {k2} (v : value (k2+>ec)) {k1} (c : context k1 k2) {r},
                dec_context ec k2 v = in_red r ->
                decctx v (ec=:c) (d_red r c)
  | dc_val  : forall {k2} {v0 : value k2} ec (v : value (k2+>ec)) 
                     {k1} {c  : context k1 k2} {d},
                dec_context ec k2 v = in_val v0 ->
                decctx v0 c d ->
                decctx v (ec=:c) d
  | dc_term : forall ec {ec0 k2} (v : value (k2+>ec)) 
                            {k1} {c : context k1 k2} {t d},
                dec_context ec k2 v = in_term t ec0 ->
                dec t (ec0=:c) d ->
                decctx v (ec=:c) d.

  Scheme dec_Ind := Induction for dec Sort Prop
    with decctx_Ind := Induction for decctx Sort Prop.


  Axiom dec_val_self : forall {k2} (v : value k2) {k1} {c : context k1 k2} {d}, 
                           dec v c d <-> decctx v c d.

  Axiom dec_not_dead : forall {t k1 k2} {c : context k1 k2} {d},
                           dec t c d -> ~ dead_ckind k2.

  Declare Module RS : RED_SEM R with Definition dec := dec.

End RED_REF_SEM.

(*
Module Type PE_REF_SEM (R : RED_LANG).

  Import R.

  Declare Module Red_Sem : RED_REF_SEM R.

  Axiom dec_context_not_val : forall k v0 ec v, 
            Red_Sem.dec_context ec k v <> in_val v0.
  Axiom dec_term_value : forall k v, 
                             Red_Sem.dec_term (value_to_term v) k = in_val v.

End PE_REF_SEM.*)


Module Type RED_SEM_PROPER (R : RED_LANG) (RS : RED_SEM R).

  Import R.
  Import RS.

  Axiom dec_is_function  : forall {t k} {d d0 : decomp k}, 
                               decempty t d -> decempty t d0 -> d = d0.
  Axiom iter_is_function : forall {k} {d : decomp k} {v v0}, 
                               iter d v -> iter d v0 -> v = v0.
  Axiom eval_is_function : forall {t} {v v0 : value init_ckind}, 
                               eval t v -> eval t v0 -> v = v0.
  Axiom dec_correct      : forall {t k1 k2} {c : context k1 k2} {d},
                               dec t c d -> decomp_to_term d = plug t c.
  Axiom dec_total        : forall t k, ~ dead_ckind k -> 
                               exists (d : decomp k), decempty t d.
  Axiom unique_decomposition :

      forall (t : term) k1, ~ dead_ckind k1 ->  

         (exists v : value k1, t = v) \/

         (exists k2 (r : redex k2) (c : context k1 k2), t = c[r] /\ 
	      forall k2' (r' : redex k2') (c' : context k1 k2'), 
                  t = c'[r'] -> k2' = k2 /\ r ~= r' /\ c ~= c').

End RED_SEM_PROPER.



Module Type PRE_ABSTRACT_MACHINE (R : RED_LANG).

  Import R.

  (** Functions specifying atomic steps of induction on terms and contexts -- needed to avoid explicit induction on terms and contexts in construction of the AM *)
  Parameter dec_term    : term -> forall k, interm_dec k.
  Parameter dec_context : forall ec k, value (k+>ec) -> interm_dec k.

  Axiom dec_term_correct : 
      forall t k, match dec_term t k with
      | in_red r       => t = r
      | in_val v       => t = v
      | in_term t0 ec0 => t = ec0:[t0]
      | in_dead        => dead_ckind k
      end.

  Axiom dec_context_correct : 
      forall ec k v, match dec_context ec k v with
      | in_red r      => ec:[v] = r
      | in_val v0     => ec:[v] = v0
      | in_term t ec0 => ec:[v] = ec0:[t]
      | in_dead       => dead_ckind (k+>ec) 
      end.
  
  (** A decomposition function specified in terms of the atomic functions above *)
  Inductive dec : term -> forall {k1 k2}, context k1 k2 -> decomp k1 -> Prop :=
  | d_dec  : forall t {k1 k2} (c : context k1 k2) {r},
               dec_term t k2 = in_red r -> 
               dec t c (d_red r c)
  | d_v    : forall t {k1 k2} {c : context k1 k2} {v d},
               dec_term t k2 = in_val v ->
               decctx v c d ->
               dec t c d
  | d_term : forall t {t0 k1 k2} {c : context k1 k2} {ec d},
               dec_term t k2 = in_term t0 ec ->
               dec t0 (ec=:c) d ->
               dec t c d

  with decctx : forall {k2}, value k2 -> forall {k1}, context k1 k2 -> decomp k1 -> Prop :=
  | dc_end  : forall {k} (v : value k), 
                ~ dead_ckind k ->
                decctx v [_] (d_val v)
  | dc_dec  : forall ec {k2} (v : value (k2+>ec)) {k1} (c : context k1 k2) {r},
                dec_context ec k2 v = in_red r ->
                decctx v (ec=:c) (d_red r c)
  | dc_val  : forall {k2} {v0 : value k2} ec (v : value (k2+>ec)) 
                     {k1} {c  : context k1 k2} {d},
                dec_context ec k2 v = in_val v0 ->
                decctx v0 c d ->
                decctx v (ec=:c) d
  | dc_term : forall ec {ec0 k2} (v : value (k2+>ec)) 
                            {k1} {c : context k1 k2} {t d},
                dec_context ec k2 v = in_term t ec0 ->
                dec t (ec0=:c) d ->
                decctx v (ec=:c) d.

  Scheme dec_Ind := Induction for dec Sort Prop
    with decctx_Ind := Induction for decctx Sort Prop.


  Inductive iter : forall {k}, decomp k -> value k -> Prop :=
  | i_val : forall {k} (v : value k), iter (d_val v) v
  | i_red : forall {k2} (r : redex k2) {t k1} {c : context k1 k2} {d v},
              contract r = Some t -> dec t c d -> iter d v ->
              iter (d_red r c) v.

  Inductive eval : term -> value init_ckind -> Prop :=
  | e_intro : forall {t} {d : decomp init_ckind} {v : value init_ckind},
                dec t [_] d -> iter d v -> eval t v.

End PRE_ABSTRACT_MACHINE.



Module Type STAGED_ABSTRACT_MACHINE (R : RED_LANG).

  Import R.

  (** Functions specifying atomic steps of induction on terms and contexts -- needed to avoid explicit induction on terms and contexts in construction of the AM *)
  Parameter dec_term    : term -> forall k, interm_dec k.
  Parameter dec_context : forall ec k, value (k+>ec) -> interm_dec k.

  Axiom dec_term_correct : 
      forall t k, match dec_term t k with
      | in_red r       => t = r
      | in_val v       => t = v
      | in_term t0 ec0 => t = ec0:[t0]
      | in_dead        => dead_ckind k
      end.

  Axiom dec_context_correct : 
      forall ec k v, match dec_context ec k v with
      | in_red r      => ec:[v] = r
      | in_val v0     => ec:[v] = v0
      | in_term t ec0 => ec:[v] = ec0:[t]
      | in_dead       => dead_ckind (k+>ec) 
      end.


  Inductive dec : term -> forall {k1 k2}, context k1 k2 -> value k1 -> Prop :=
  | d_dec  : forall t {k1 k2} {c : context k1 k2} {r v},
               dec_term t k2 = in_red r -> iter (d_red r c) v ->
               dec t c v
  | d_v    : forall t {k1 k2} {c : context k1 k2} {v v0},
               dec_term t k2 = in_val v -> decctx v c v0 ->
               dec t c v0
  | d_many : forall t {t0 ec k1 k2} {c : context k1 k2} {v},
               dec_term t k2 = in_term t0 ec -> dec t0 (ec=:c) v ->
               dec t c v

  with decctx : forall {k2}, value k2 -> forall {k1}, context k1 k2 -> value k1 -> Prop :=
  | dc_end  : forall {k} {v v0 : value k},
                ~ dead_ckind k ->
                iter (d_val v) v0 ->
                decctx v [_] v0
  | dc_dec  : forall ec {k2} (v : value (k2+>ec)) {k1} {c : context k1 k2} {r v0},
                dec_context ec k2 v = in_red r -> iter (d_red r c) v0 ->
                decctx v (ec=:c) v0
  | dc_val  : forall ec {k2} (v : value (k2+>ec)) {v0 k1} {c : context k1 k2} {v1},
                dec_context ec k2 v = in_val v0 -> decctx v0 c v1 ->
                decctx v (ec=:c) v1
  | dc_term : forall ec {k2} (v : value (k2+>ec)) {t ec0 k1} {c : context k1 k2} {v0},
                dec_context ec k2 v = in_term t ec0 -> dec t (ec0=:c) v0 ->
                decctx v (ec=:c) v0

  with iter : forall {k}, decomp k -> value k -> Prop :=
  | i_val : forall {k} (v : value k), 
               iter (d_val v) v
  | i_red : forall {k2} (r : redex k2) {k1} {c : context k1 k2} {t v},
               contract r = Some t -> dec t c v -> 
               iter (d_red r c) v.

  Scheme dec_Ind    := Induction for dec Sort Prop
    with decctx_Ind := Induction for decctx Sort Prop
    with iter_Ind   := Induction for iter Sort Prop.


  Inductive eval : term -> value init_ckind -> Prop :=
  | e_intro : forall {t} {v : value init_ckind}, dec t [_] v -> eval t v.

End STAGED_ABSTRACT_MACHINE.



Module Type EVAL_APPLY_MACHINE (R : RED_LANG).

  Import R.

  (** Functions specifying atomic steps of induction on terms and contexts -- needed to avoid explicit induction on terms and contexts in construction of the AM *)
  Parameter dec_term    : term -> forall k, interm_dec k.
  Parameter dec_context : forall ec k, value (k+>ec) -> interm_dec k.

  Axiom dec_term_correct : 
      forall t k, match dec_term t k with
      | in_red r       => t = r
      | in_val v       => t = v
      | in_term t0 ec0 => t = ec0:[t0]
      | in_dead        => dead_ckind k
      end.

  Axiom dec_context_correct : 
      forall ec k v, match dec_context ec k v with
      | in_red r      => ec:[v] = r
      | in_val v0     => ec:[v] = v0
      | in_term t ec0 => ec:[v] = ec0:[t]
      | in_dead       => dead_ckind (k+>ec) 
      end.


  Inductive dec : term -> forall {k1 k2}, context k1 k2 -> value k1 -> Prop :=
  | d_d_r  : forall t {t0 k1 k2} {c : context k1 k2} {r v},
               dec_term t k2 = in_red r -> contract r = Some t0 -> dec t0 c v ->
               dec t c v
  | d_v    : forall t {k1 k2} {c : context k1 k2} {v v0},
               dec_term t k2 = in_val v -> decctx v c v0 ->
               dec t c v0
  | d_term : forall t {t0 ec k1 k2} {c : context k1 k2} {v},
               dec_term t k2 = in_term t0 ec -> dec t0 (ec=:c) v ->
               dec t c v

  with decctx : forall {k2}, value k2 -> forall {k1}, context k1 k2 -> value k1 -> Prop :=
  | dc_end : forall {k} (v : value k), 
               ~ dead_ckind k ->
               decctx v [_] v
  | dc_red : forall ec {k2} (v : value (k2+>ec)) {k1} {c : context k1 k2} {r t v0},
               dec_context ec k2 v = in_red r -> contract r = Some t -> dec t c v0 ->
               decctx v (ec=:c) v0
  | dc_rec : forall ec {k2} (v : value (k2+>ec)) {k1} {c : context k1 k2} {v0 v1},
               dec_context ec k2 v = in_val v0 -> decctx v0 c v1 ->
               decctx v (ec=:c) v1
  | dc_trm : forall ec {k2} (v : value (k2+>ec)) {k1} {c : context k1 k2} {t ec0 v0},
               dec_context ec k2 v = in_term t ec0 -> dec t (ec0=:c) v0 ->
               decctx v (ec=:c) v0.


  Scheme dec_Ind := Induction for dec Sort Prop
    with decctx_Ind := Induction for decctx Sort Prop.


  Inductive eval : term -> value init_ckind -> Prop :=
  | e_intro : forall {t} {v : value init_ckind}, dec t [_] v -> eval t v.

End EVAL_APPLY_MACHINE.



Module Type PROPER_EA_MACHINE (R : RED_LANG).

  Import R.

  (** Functions specifying atomic steps of induction on terms and contexts -- needed to avoid explicit induction on terms and contexts in construction of the AM *)
  Parameter dec_term    : term -> forall k, interm_dec k.
  Parameter dec_context : forall ec k, value (k+>ec) -> interm_dec k.

  Axiom dec_term_correct : 
      forall t k, match dec_term t k with
      | in_red r       => t = r
      | in_val v       => t = v
      | in_term t0 ec0 => t = ec0:[t0]
      | in_dead        => dead_ckind k
      end.

  Axiom dec_context_correct : 
      forall ec k v, match dec_context ec k v with
      | in_red r      => ec:[v] = r
      | in_val v0     => ec:[v] = v0
      | in_term t ec0 => ec:[v] = ec0:[t]
      | in_dead       => dead_ckind (k+>ec) 
      end.

  Inductive configuration : Set :=
  | c_eval  : term -> forall {k1 k2}, context k1 k2 -> configuration
  | c_apply : forall {k1 k2}, context k1 k2 -> value k2 -> configuration.
(*  | c_final : value init_ckind -> configuration.*)

  Definition c_init t                       := c_eval t (@empty init_ckind).
  Definition c_final (v : value init_ckind) := c_apply [_] v.


  Reserved Notation " a → b " (at level 40, no associativity).


  Inductive transition : configuration -> configuration -> Prop :=
(*  | t_init : forall t, 
               c_init t → c_eval t (@empty init_ckind)*)
  | t_red  : forall t {k1 k2} (c : context k1 k2) {r t0},
               dec_term t k2 = in_red r -> contract r = Some t0 ->
               c_eval t c → c_eval t0 c
  | t_val  : forall t {k1 k2} (c : context k1 k2) {v},
      	       dec_term t k2 = in_val v ->
               c_eval t c → c_apply c v
  | t_term : forall t {k1 k2} (c : context k1 k2) {t0 ec},
               dec_term t k2 = in_term t0 ec ->
               c_eval t c → c_eval t0 (ec=:c)
(*  | t_cfin : forall (v : value init_ckind),
               ~ dead_ckind init_ckind ->
               c_apply [_] v → c_final v*)
  | t_cred : forall ec {k2} (v : value (k2+>ec)) {k1} (c : context k1 k2) {r t},
               dec_context ec k2 v = in_red r -> contract r = Some t ->
               c_apply (ec=:c) v → c_eval t c
  | t_cval : forall ec {k2} (v : value (k2+>ec)) {k1} (c : context k1 k2) {v0},
               dec_context ec k2 v = in_val v0 ->
               c_apply (ec=:c) v → c_apply c v0
  | t_cterm: forall ec {k2} (v : value (k2+>ec)) {k1} (c : context k1 k2) {t ec0},
               dec_context ec k2 v = in_term t ec0 ->
               c_apply (ec=:c) v → c_eval t (ec0=:c)
  where " a → b " := (transition a b).


  Declare Module AM : ABSTRACT_MACHINE
    with Definition term := term
    with Definition value := value init_ckind
    with Definition configuration := configuration
    with Definition transition := transition
    with Definition c_init := c_init
    with Definition c_final := c_final.

End PROPER_EA_MACHINE.
