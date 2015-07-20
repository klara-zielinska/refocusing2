Require Export refocusing_lang.

Module Type RED_SEM (R : RED_LANG).

  Parameter dec : R.term -> forall {k1 k2}, R.context k1 k2 -> R.decomp k1 -> Prop.

  (** A redex in context will only ever be reduced to itself *)
  Axiom dec_redex_self : forall {k1 k2} (r : R.redex k2) (c : R.context k1 k2), 
                             dec (R.redex_to_term r) c (R.d_red r c).

  Import R.
  Axiom decompose : forall (t : R.term) k1, ~ R.dead_ckind k1 ->
      (exists (v : R.value k1), t = R.value_to_term v) \/
      (exists k2 (r : R.redex k2) (c : R.context k1 k2), R.plug (R.redex_to_term r) c = t).

  (** dec is left inverse of plug *)
  Axiom dec_correct : forall t k1 k2 (c : R.context k1 k2) d, dec t c d -> 
                          R.decomp_to_term d = R.plug t c.

  Import R.
  Axiom dec_plug     : forall k1 k2 (c : R.context k1 k2) k3 (c0 : R.context k3 k1) t d, 
                          ~ dead_ckind k2 -> dec (R.plug t c) c0 d -> 
                          dec t (R.compose c c0) d.
  Axiom dec_plug_rev : forall k1 k2 (c : R.context k1 k2) k3 (c0 : R.context k3 k1) t d, 
                          ~ dead_ckind k2 ->  dec t (R.compose c c0) d -> 
                          dec (R.plug t c) c0 d.

  Inductive decempty : R.term -> forall {k}, R.decomp k -> Prop :=
  | d_intro : forall (t : R.term) {k} (d : R.decomp k), dec t (@R.empty k) d -> decempty t d.

  Inductive iter : forall {k}, R.decomp k -> R.value k -> Prop :=
  | i_val : forall {k} (v : R.value k), iter (R.d_val v) v
  | i_red : forall {k} (r : R.redex k) t {k'} (c : R.context k' k) d v,
              R.contract r = Some t -> decempty (R.plug t c) d -> iter d v ->
              iter (R.d_red r c) v.

  Inductive eval : R.term -> forall {k}, R.value k -> Prop :=
  | e_intro : forall t {k} (d : R.decomp k) v, decempty t d -> iter d v -> eval t v.

End RED_SEM.

Module Type RED_REF_SEM (R : RED_LANG).

  Import R.

  (** Functions specifying atomic steps of induction on terms and contexts -- needed to avoid explicit induction on terms and contexts in construction of the AM *)
  Parameter dec_term    : R.term -> forall k, R.interm_dec k.
  Parameter dec_context : forall (ec : R.elem_context) (k : R.ckind),
                              R.value (R.ckind_trans k ec) -> R.interm_dec k.


  (*Axiom dec_term_liveness : 
      forall t k, ~ R.dead_ckind k -> 
      forall t0 ec0, dec_term t k = R.in_term t0 ec0 ->
      ~ R.dead_ckind (R.ckind_trans k ec0).*)

  Axiom dec_term_correct : forall t k, match dec_term t k with
    | R.in_red r => R.redex_to_term r = t
    | R.in_val v => R.value_to_term v = t
    | R.in_term t0 ec0 => R.atom_plug t0 ec0 = t
    | R.in_dead => R.dead_ckind k
  end.
  Axiom dec_context_correct : forall ec k v, match dec_context ec k v with
    | R.in_red r => R.redex_to_term r = R.atom_plug (R.value_to_term v) ec
    | R.in_val v0 => R.value_to_term v0 = R.atom_plug (R.value_to_term v) ec
    | R.in_term t ec0 => R.atom_plug t ec0 = R.atom_plug (R.value_to_term v) ec
    | R.in_dead => R.dead_ckind (R.ckind_trans k ec) 
  end.

  (** A decomposition function specified in terms of the atomic functions above *)
  Inductive dec : R.term -> forall {k1 k2}, R.context k1 k2 -> R.decomp k1 -> Prop :=
  | d_dec  : forall t {k1 k2} (c : R.context k1 k2) (r : R.redex k2),
               dec_term t k2 = R.in_red r -> 
               dec t c (R.d_red r c)
  | d_v    : forall t {k1 k2} (c : R.context k1 k2) (v : R.value k2) (d : R.decomp k1),
               dec_term t k2 = R.in_val v ->
               decctx v c d ->
               dec t c d
  | d_term : forall t t0 {k1 k2} (c : R.context k1 k2) ec (d : R.decomp k1),
               dec_term t k2 = R.in_term t0 ec ->
               dec t0 (R.ccons ec c) d ->
               dec t c d
  with decctx : forall {k2}, R.value k2 -> forall {k1}, R.context k1 k2 -> R.decomp k1 -> Prop :=
  | dc_end  : forall {k} (v : R.value k), 
                ~ R.dead_ckind k ->
                decctx v (@R.empty k) (R.d_val v)
  | dc_dec  : forall ec {k2} (v : R.value (R.ckind_trans k2 ec)) 
                        {k1} (c : R.context k1 k2) (r : R.redex k2),
                dec_context ec k2 v = R.in_red r ->
                decctx v (R.ccons ec c) (R.d_red r c)
  | dc_val  : forall {k2} (v0 : R.value k2) ec   (v : R.value (R.ckind_trans k2 ec)) 
                     {k1} (c  : R.context k1 k2) (d : R.decomp k1),
                dec_context ec k2 v = R.in_val v0 ->
                decctx v0 c d ->
                decctx v (R.ccons ec c) d
  | dc_term : forall ec ec0 {k2} (v : R.value (R.ckind_trans k2 ec)) 
                            {k1} (c : R.context k1 k2) (t : R.term) (d : R.decomp k1),
                dec_context ec k2 v = R.in_term t ec0 ->
                dec t (R.ccons ec0 c) d ->
                decctx v (R.ccons ec c) d.

  Axiom dec_val_self : forall k2 (v : R.value k2) k1 (c : R.context k1 k2) (d : R.decomp k1), 
                           dec (R.value_to_term v) c d <-> decctx v c d.

  Declare Module RS : RED_SEM R with Definition dec := dec.

  Scheme dec_Ind := Induction for dec Sort Prop
  with decctx_Ind := Induction for decctx Sort Prop.

End RED_REF_SEM.


Module Type PE_REF_SEM (R : RED_LANG).

  Declare Module Red_Sem : RED_REF_SEM R.

  Axiom dec_context_not_val : forall k (v0 : R.value k) (ec : R.elem_context) 
                                       (v  : R.value (R.ckind_trans k ec)), 
            Red_Sem.dec_context ec k v <> R.in_val v0.
  Import R.
  Axiom dec_term_value : forall k v, 
                             Red_Sem.dec_term (R.value_to_term v) k = R.in_val v.

End PE_REF_SEM.

Require Import Program.

Module Type RED_PROP (R : RED_LANG) (RS : RED_REF_SEM(R)).

  Axiom dec_is_function  : forall t k (d d0 : R.decomp k), 
                               RS.RS.decempty t d -> RS.RS.decempty t d0 -> d = d0.
  Axiom iter_is_function : forall k d (v v0 : R.value k), 
                               RS.RS.iter d v -> RS.RS.iter d v0 -> v = v0.
  Axiom eval_is_function : forall t k (v v0 : R.value k), 
                               RS.RS.eval t v -> RS.RS.eval t v0 -> v = v0.
  Axiom dec_correct : forall t k1 k2 (c : R.context k1 k2) d, 
                          RS.RS.dec t c d -> R.decomp_to_term d = R.plug t c.
  Axiom dec_total : forall t k, ~ R.dead_ckind k -> exists (d : R.decomp k), RS.RS.decempty t d.
  Axiom unique_decomposition : forall t k, ~ R.dead_ckind k ->  
      (exists v : R.value k, t = R.value_to_term v) \/ 
      (exists k2 (r : R.redex k2) (c : R.context k k2),  R.plug (R.redex_to_term r) c = t /\ 
	  forall k2' (r0 : R.redex k2') (c0 : R.context k k2'), 
              R.plug (R.redex_to_term r0) c0 = t -> k2' = k2 /\ r ~= r0 /\ c ~= c0).

End RED_PROP.