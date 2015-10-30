Require Import reduction_semantics.
Require Export refocusing_step.
Require Import refocusing_semantics.
Require Export abstract_machine.




Module Type PRE_ABSTRACT_MACHINE (R : RED_LANG) (RS : RED_REF_SEM R).

  Module DEC := RS.DEC.
  Import R.
  Export DEC.


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

  with decctx : forall {k2}, value k2 -> 
                    forall {k1}, context k1 k2 -> decomp k1 -> Prop :=

  | dc_end  : forall {k} (v : value k), 
                ~ dead_ckind k ->
                decctx v [.] (d_val v)
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

  Scheme dec_Ind    := Induction for dec Sort Prop
    with decctx_Ind := Induction for decctx Sort Prop.


  Inductive iter : forall {k}, decomp k -> value k -> Prop :=
  | i_val : forall {k} (v : value k), 
              iter (d_val v) v
  | i_red : forall {k2} (r : redex k2) {t k1} {c : context k1 k2} {d v},
              contract r = Some t -> 
              dec t c d -> 
              iter d v ->
              iter (d_red r c) v.


  Inductive eval : term -> value init_ckind -> Prop :=
  | e_intro : forall {t d v}, dec t [.] d -> iter d v -> eval t v.

End PRE_ABSTRACT_MACHINE.




Module Type STAGED_ABSTRACT_MACHINE (R : RED_LANG) (RS : RED_REF_SEM R).

  Module DEC := RS.DEC.
  Import R.
  Export DEC.


  Inductive dec : term -> forall {k1 k2}, context k1 k2 -> value k1 -> Prop :=

  | d_dec  : forall t {k1 k2} {c : context k1 k2} {r v},
               dec_term t k2 = in_red r -> 
               iter (d_red r c) v ->
               dec t c v
  | d_v    : forall t {k1 k2} {c : context k1 k2} {v v0},
               dec_term t k2 = in_val v -> 
               decctx v c v0 ->
               dec t c v0
  | d_many : forall t {t0 ec k1 k2} {c : context k1 k2} {v},
               dec_term t k2 = in_term t0 ec -> 
               dec t0 (ec=:c) v ->
               dec t c v

  with decctx : forall {k2}, value k2 -> 
                    forall {k1}, context k1 k2 -> value k1 -> Prop :=

  | dc_end  : forall {k} {v v0 : value k},
                ~ dead_ckind k ->
                iter (d_val v) v0 ->
                decctx v [.] v0
  | dc_dec  : forall ec {k2} (v : value (k2+>ec)) {k1} {c : context k1 k2} {r v0},
                dec_context ec k2 v = in_red r -> 
                iter (d_red r c) v0 ->
                decctx v (ec=:c) v0
  | dc_val  : forall ec {k2} (v : value (k2+>ec)) {v0 k1} {c : context k1 k2} {v1},
                dec_context ec k2 v = in_val v0 -> 
                decctx v0 c v1 ->
                decctx v (ec=:c) v1
  | dc_term : forall ec {k2} (v : value (k2+>ec)) {t ec0 k1} {c : context k1 k2} {v0},
                dec_context ec k2 v = in_term t ec0 -> 
                dec t (ec0=:c) v0 ->
                decctx v (ec=:c) v0

  with iter : forall {k}, decomp k -> value k -> Prop :=

  | i_val : forall {k} (v : value k), 
              iter (d_val v) v
  | i_red : forall {k2} (r : redex k2) {k1} {c : context k1 k2} {t v},
              contract r = Some t -> 
              dec t c v -> 
              iter (d_red r c) v.

  Scheme dec_Ind    := Induction for dec Sort Prop
    with decctx_Ind := Induction for decctx Sort Prop
    with iter_Ind   := Induction for iter Sort Prop.


  Inductive eval : term -> value init_ckind -> Prop :=
  | e_intro : forall {t v}, dec t [.] v -> eval t v.

End STAGED_ABSTRACT_MACHINE.




Module Type EVAL_APPLY_MACHINE (R : RED_LANG) (RS : RED_REF_SEM R).

  Module DEC := RS.DEC.
  Import R.
  Export DEC.


  Inductive dec : term -> forall {k1 k2}, context k1 k2 -> value k1 -> Prop :=

  | d_d_r  : forall t {t0 k1 k2} {c : context k1 k2} {r : redex k2} {v},
               dec_term t k2 = in_red r -> 
               contract r = Some t0 -> 
               dec t0 c v ->
               dec t c v
  | d_v    : forall t {k1 k2} {c : context k1 k2} {v v0},
               dec_term t k2 = in_val v -> 
               decctx v c v0 ->
               dec t c v0
  | d_term : forall t {t0 ec k1 k2} {c : context k1 k2} {v},
               dec_term t k2 = in_term t0 ec -> 
               dec t0 (ec=:c) v ->
               dec t c v

  with decctx : forall {k2}, value k2 -> 
                    forall {k1}, context k1 k2 -> value k1 -> Prop :=

  | dc_end : forall {k} (v : value k), 
               ~ dead_ckind k ->
               decctx v [.] v
  | dc_red : forall ec {k2} (v : value (k2+>ec)) {k1} {c : context k1 k2} {r t v0},
               dec_context ec k2 v = in_red r -> 
               contract r = Some t -> 
               dec t c v0 ->
               decctx v (ec=:c) v0
  | dc_rec : forall ec {k2} (v : value (k2+>ec)) {k1} {c : context k1 k2} {v0 v1},
               dec_context ec k2 v = in_val v0 -> 
               decctx v0 c v1 ->
               decctx v (ec=:c) v1
  | dc_trm : forall ec {k2} (v : value (k2+>ec)) {k1} {c : context k1 k2} {t ec0 v0},
               dec_context ec k2 v = in_term t ec0 -> 
               dec t (ec0=:c) v0 ->
               decctx v (ec=:c) v0.

  Scheme dec_Ind    := Induction for dec Sort Prop
    with decctx_Ind := Induction for decctx Sort Prop.


  Inductive eval : term -> value init_ckind -> Prop :=
  | e_intro : forall {t v}, dec t [.] v -> eval t v.

End EVAL_APPLY_MACHINE.




Module Type PROPER_EA_MACHINE (R : RED_LANG) (RS : RED_REF_SEM R) <: DET_ABSTRACT_MACHINE.

  Import R.
  Import RS.DEC.


  Definition term  := term.
  Definition value := value init_ckind.

  Inductive conf : Set :=
  | c_eval  : term -> forall {k1 k2}, context k1 k2 -> conf
  | c_apply : forall {k1 k2}, context k1 k2 -> R.value k2 -> conf.
  Definition configuration := conf.

  Definition c_init t            := c_eval t [.](init_ckind).
  Definition c_final (v : value) := c_apply [.] v.
  (*Definition final_of (st : configuration) : option value := 
      match st with 
      | c_apply k _ [.] v => 
          match is_initial k with
          | left H => match H in _ = k return R.value k -> option value with
                      | eq_refl => fun v => Some v
                      end v
          | _      => None
          end
      | _ => None
      end.
  Axiom final_of_correct : forall c v, final_of c = Some v <-> c_final v = c.*)


  Reserved Notation "st1 → st2" (at level 40, no associativity).

  Inductive trans : configuration -> configuration -> Prop :=

  | t_red  : forall t {k1 k2} (c : context k1 k2) {r : redex k2} { t0},
               dec_term t k2 = in_red r -> contract r = Some t0 ->
               c_eval t c → c_eval t0 c
  | t_val  : forall t {k1 k2} (c : context k1 k2) {v},
      	       dec_term t k2 = in_val v ->
               c_eval t c → c_apply c v
  | t_term : forall t {k1 k2} (c : context k1 k2) {t0 ec},
               dec_term t k2 = in_term t0 ec ->
               c_eval t c → c_eval t0 (ec=:c)
  | t_cred : forall ec {k2} (v : R.value (k2+>ec)) {k1} (c : context k1 k2) {r t},
               dec_context ec k2 v = in_red r -> contract r = Some t ->
               c_apply (ec=:c) v → c_eval t c
  | t_cval : forall ec {k2} (v : R.value (k2+>ec)) {k1} (c : context k1 k2) {v0},
               dec_context ec k2 v = in_val v0 ->
               c_apply (ec=:c) v → c_apply c v0
  | t_cterm: forall ec {k2} (v : R.value (k2+>ec)) {k1} (c : context k1 k2) {t ec0},
               dec_context ec k2 v = in_term t ec0 ->
               c_apply (ec=:c) v → c_eval t (ec0=:c)

  where "st1 → st2" := (trans st1 st2).
  Definition transition := trans.
  Hint Unfold transition.

  Axiom final_correct : forall v st, ~ c_final v → st.



  Reserved Notation "c1 →+ c2" (at level 40, no associativity).
  Reserved Notation "c1 →* c2" (at level 40, no associativity).

  Inductive trans_close : configuration -> configuration -> Prop :=
  | one_step   : forall c1 c2,     c1 → c2  ->  c1 →+ c2
  | multi_step : forall c1 c2 c3,  c1 → c2  ->  c2 →+ c3  ->  c1 →+ c3
  where "c1 →+ c2" := (trans_close c1 c2).

  Definition trans_ref_close c1 c2 := c1 = c2 \/ trans_close c1 c2.
  Notation "c1 →* c2" := (trans_ref_close c1 c2).


  Inductive eval : term -> value -> Prop :=
  | e_intro : forall t v, trans_close (c_init t) (c_final v) -> eval t v.


  Definition next_conf st :=
      match st with
      | c_eval t _ k2 c  => 
            match dec_term t k2 with
            | in_red r => option_map (fun t' => c_eval t' c) (contract r)
            | in_val v => Some (c_apply c v)
            | in_term t ec => Some (c_eval t (ec=:c))
            | in_dead => None
            end
      | c_apply _ _ (ccons ec k c) v => 
            match dec_context ec k v with
            | in_red r => option_map (fun t' => c_eval t' c) (contract r)
            | in_val v => Some (c_apply c v)
            | in_term t ec => Some (c_eval t (ec=:c))
            | in_dead => None
            end
      | c_apply _ _ [.] v => 
            None
      end.


  Axiom next_correct  : forall c1 c2, next_conf c1 = Some c2 <-> c1 → c2.

End PROPER_EA_MACHINE.




Module Type PUSH_ENTER_MACHINE (R : RED_LANG) (PERS : PE_REF_SEM R).

  Module DEC := PERS.RefSem.DEC.
  Import R.
  Export DEC.


  Axiom dec_context_not_val : 
      forall ec {k} v1 v0, dec_context ec k v0 <> in_val v1.

  Axiom dec_term_value : 
      forall {k} (v : value k), dec_term v k = in_val v.


  Inductive dec : term -> forall {k1 k2}, context k1 k2 -> value k1 -> Prop :=

  | dec_r    : forall t {t0 k1 k2} {c : context k1 k2} {r  v},
                 dec_term t k2 = in_red r -> 
                 contract r = Some t0 -> 
                 dec t0 c v ->
                 dec t c v
  | dec_val  : forall t {k} {v : value k},
                 dec_term t k = in_val v ->
                 dec t [.] v
  | dec_v_t  : forall t ec {t0 ec0} {k1 k2} {c : context k1 k2} {v v0},
                 dec_term t (k2+>ec) = in_val v -> 
                 dec_context ec k2 v = in_term t0 ec0 -> 
                 dec t0 (ec0=:c) v0 ->
                 dec t (ec=:c) v0
  | dec_red  : forall t ec {t0} {k1 k2} {c : context k1 k2} {v v0 r},
                 dec_term t (k2+>ec) = in_val v ->
                 dec_context ec k2 v = in_red r -> 
                 contract r = Some t0 -> 
                 dec t0 c v0 ->
                 dec t (ec=:c) v0
  | dec_rec  : forall t {t0 ec} {k1 k2} {c : context k1 k2} {v},
                 dec_term t k2 = in_term t0 ec ->
                 dec t0 (ec=:c) v ->
                 dec t c v.


  Inductive eval : term -> value init_ckind -> Prop :=
  | e_intro : forall {t v}, dec t [.] v -> eval t v.

End PUSH_ENTER_MACHINE.




Module Type PROPER_PE_MACHINE (R : RED_LANG) (PERS : PE_REF_SEM R) <: DET_ABSTRACT_MACHINE.

  Import R.
  Import PERS.RefSem.DEC.


  Definition term  := term.
  Definition value := value init_ckind.


  Inductive conf : Set :=
  | c_eval  : term -> forall {k1 k2}, context k1 k2 -> conf
  | c_fin : forall {k}, R.value k                   -> conf.
  Definition configuration := conf.

  Definition c_init t  := c_eval t [.](init_ckind).
  Definition c_final (v : value) := c_fin v.
  (*Definition final_of (st : configuration) : option value := 
      match st with 
      | c_fin k v => 
          match is_initial k with
          | left H => match H in _ = k return R.value k -> option value with
                      | eq_refl => fun v => Some v
                      end v
          | _      => None
          end
      | _ => None
      end.
  Axiom final_of_correct : forall c v, final_of c = Some v <-> c_final v = c.*)


  Reserved Notation "c1 → c2" (at level 40, no associativity).

  Inductive trans : configuration -> configuration -> Prop :=

  | t_red  : forall t {k1 k2} (c : context k1 k2) {t0 r},
               dec_term t k2 = in_red r -> 
               contract r = Some t0 ->
               c_eval t c → c_eval t0 c
  | t_cval : forall t {k} {v : R.value k},
               dec_term t k = in_val v ->
               c_eval t [.](k) → c_fin v
  | t_cred : forall t ec {t0} {k1 k2} (c : context k1 k2) {v r},
               dec_term t (k2+>ec) = in_val v ->
               dec_context ec k2 v = in_red r ->
               contract r = Some t0 ->
               c_eval t (ec=:c) → c_eval t0 c
  | t_crec : forall t ec {t0 ec0 k1 k2} (c : context k1 k2) {v},
               dec_term t (k2+>ec) = in_val v ->
               dec_context ec k2 v = in_term t0 ec0 ->
               c_eval t (ec=:c) → c_eval t0 (ec0=:c)
  | t_rec  : forall t {t0 ec k1 k2} (c : context k1 k2),
               dec_term t k2 = in_term t0 ec ->
               c_eval t c → c_eval t0 (ec=:c)

  where "c1 → c2" := (trans c1 c2).
  Definition transition := trans.
  Hint Unfold transition.

  Axiom final_correct : forall v st, ~ c_final v → st.


  Reserved Notation "c1 →+ c2" (at level 40, no associativity).
  Reserved Notation "c1 →* c2" (at level 40, no associativity).

  Inductive trans_close : configuration -> configuration -> Prop :=
  | one_step   : forall c1 c2,     c1 → c2  ->  c1 →+ c2
  | multi_step : forall c1 c2 c3,  c1 → c2  ->  c2 →+ c3  ->  c1 →+ c3
  where "c1 →+ c2" := (trans_close c1 c2).

  Definition trans_ref_close c1 c2 := c1 = c2 \/ trans_close c1 c2.
  Notation "c1 →* c2" := (trans_ref_close c1 c2).

  Inductive eval : term -> value -> Prop :=
  | e_intro : forall t v, trans_close (c_init t) (c_final v) -> eval t v.


  Definition next_conf st :=
      match st with
      | c_eval t _ k2 c  => 
            match dec_term t k2 with
            | in_red r => option_map (fun t' => c_eval t' c) (contract r)
            | in_val v => match c in context _ k2 
                              return R.value k2 -> option configuration with 
                          | [.]          => fun _ => Some (c_fin v)
                          | ccons ec k c => fun v => 
                                match dec_context ec k v with
                                | in_red r       => option_map (fun t' => c_eval t' c)
                                                               (contract r)
                                | in_term t' ec' => Some (c_eval t' (ec'=:c))
                                | _              => None
                                end
                          end v
            | in_term t ec => Some (c_eval t (ec=:c))
            | in_dead => None
            end
      | _ => None
      end.


  Axiom next_correct  : forall c1 c2, next_conf c1 = Some c2 <-> c1 → c2.

End PROPER_PE_MACHINE.
