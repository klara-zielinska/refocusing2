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
      (exists k2 (r : redex k2) (c : context k1 k2), plug r c = t).

  (** dec is left inverse of plug *)
  Axiom dec_correct  : forall t {k1 k2} (c : context k1 k2) d, dec t c d -> 
                           decomp_to_term d = plug t c.

  Axiom dec_plug     : forall {k1 k2} (c : context k1 k2) {k3} (c0 : context k3 k1) t d, 
                           ~ dead_ckind k2 -> dec (plug t c) c0 d -> 
                           dec t (c ~+ c0) d.

  Axiom dec_plug_rev : forall {k1 k2} (c : context k1 k2) {k3} (c0 : context k3 k1) t d, 
                           ~ dead_ckind k2 ->  dec t (c ~+ c0) d -> 
                           dec (plug t c) c0 d.

  Inductive decempty : term -> forall {k}, decomp k -> Prop :=
  | d_intro : forall t {k} (d : decomp k), dec t [_] d -> decempty t d.

  Inductive iter : forall {k}, decomp k -> value k -> Prop :=
  | i_val : forall {k} (v : value k), iter (d_val v) v
  | i_red : forall {k2} (r : redex k2) t {k1} (c : context k1 k2) d v,
              contract r = Some t -> decempty (plug t c) d -> iter d v ->
              iter (d_red r c) v.

  Inductive eval : term -> forall {k}, value k -> Prop :=
  | e_intro : forall t {k} (d : decomp k) v, decempty t d -> iter d v -> eval t v.

End RED_SEM.


Module Type RED_REF_SEM (R : RED_LANG).

  Import R. 

  (** Functions specifying atomic steps of induction on terms and contexts -- needed to avoid explicit induction on terms and contexts in construction of the AM *)
  Parameter dec_term    : term -> forall k, interm_dec k.
  Parameter dec_context : forall ec k, value (k+>ec) -> interm_dec k.


  (*Axiom dec_term_liveness : 
      forall t k, ~ dead_ckind k -> 
      forall t0 ec0, dec_term t k = in_term t0 ec0 ->
      ~ dead_ckind (ckind_trans k ec0).*)

  Axiom dec_term_correct : forall t k, match dec_term t k with
    | in_red r => redex_to_term r = t
    | in_val v => value_to_term v = t
    | in_term t0 ec0 => atom_plug t0 ec0 = t
    | in_dead => dead_ckind k
  end.
  Axiom dec_context_correct : forall ec k v, match dec_context ec k v with
    | in_red r => redex_to_term r = atom_plug (value_to_term v) ec
    | in_val v0 => value_to_term v0 = atom_plug (value_to_term v) ec
    | in_term t ec0 => atom_plug t ec0 = atom_plug (value_to_term v) ec
    | in_dead => dead_ckind (k+>ec) 
  end.

  (** A decomposition function specified in terms of the atomic functions above *)
  Inductive dec : term -> forall {k1 k2}, context k1 k2 -> decomp k1 -> Prop :=
  | d_dec  : forall t {k1 k2} (c : context k1 k2) r,
               dec_term t k2 = in_red r -> 
               dec t c (d_red r c)
  | d_v    : forall t {k1 k2} (c : context k1 k2) v d,
               dec_term t k2 = in_val v ->
               decctx v c d ->
               dec t c d
  | d_term : forall t t0 {k1 k2} (c : context k1 k2) ec d,
               dec_term t k2 = in_term t0 ec ->
               dec t0 (ccons ec c) d ->
               dec t c d
  with decctx : forall {k2}, value k2 -> forall {k1}, context k1 k2 -> decomp k1 -> Prop :=
  | dc_end  : forall {k} (v : value k), 
                ~ dead_ckind k ->
                decctx v [_] (d_val v)
  | dc_dec  : forall ec {k2} (v : value (k2+>ec)) {k1} (c : context k1 k2) r,
                dec_context ec k2 v = in_red r ->
                decctx v (ccons ec c) (d_red r c)
  | dc_val  : forall {k2} (v0 : value k2) ec (v : value (k2+>ec)) 
                     {k1} (c  : context k1 k2) d,
                dec_context ec k2 v = in_val v0 ->
                decctx v0 c d ->
                decctx v (ccons ec c) d
  | dc_term : forall ec ec0 {k2} (v : value (k2+>ec)) 
                            {k1} (c : context k1 k2) t d,
                dec_context ec k2 v = in_term t ec0 ->
                dec t (ccons ec0 c) d ->
                decctx v (ccons ec c) d.

  Axiom dec_val_self : forall {k2} (v : value k2) {k1} (c : context k1 k2) d, 
                           dec (value_to_term v) c d <-> decctx v c d.

  Declare Module RS : RED_SEM R with Definition dec := dec.

  Scheme dec_Ind := Induction for dec Sort Prop
  with decctx_Ind := Induction for decctx Sort Prop.

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


Module Type RED_PROP (R : RED_LANG) (RS : RED_SEM(R)).

  Import R.
  Import RS.

  Axiom dec_is_function  : forall t {k} (d d0 : decomp k), 
                               decempty t d -> decempty t d0 -> d = d0.
  Axiom iter_is_function : forall {k} (d : decomp k) v v0, 
                               iter d v -> iter d v0 -> v = v0.
  Axiom eval_is_function : forall t {k} (v v0 : value k), 
                               eval t v -> eval t v0 -> v = v0.
  Axiom dec_correct      : forall t {k1 k2} (c : context k1 k2) d,
                               dec t c d -> decomp_to_term d = plug t c.
  Axiom dec_total        : forall t k, ~ dead_ckind k -> 
                               exists (d : decomp k), decempty t d.
  Axiom unique_decomposition : 
      forall t k1, ~ dead_ckind k1 ->  

         (exists v : R.value k1, value_to_term v = t) \/

         (exists k2 (r : redex k2) (c : context k1 k2), plug r c = t /\ 
	      forall k2' (r' : redex k2') (c' : context k1 k2'), 
                  plug r' c' = t -> k2' = k2 /\ r ~= r' /\ c ~= c').

End RED_PROP.