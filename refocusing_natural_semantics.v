
(*** Signatures ***)


Require Import reduction_semantics.
Require Import refocusing_semantics.




Module Type PRE_REF_NATURAL_SEM (R : RED_LANG) (RS : RED_REF_SEM R).

  Module ST := RS.ST.
  Export ST.
  Import R.


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
              contract r = Some t  ->  dec t c d  ->  iter d v ->
              iter (d_red r c) v.


  Inductive eval : term -> value init_ckind -> Prop :=
  | e_intro : forall {t d v}, dec t [.] d -> iter d v -> eval t v.

End PRE_REF_NATURAL_SEM.





Module Type STAGED_REF_NATURAL_SEM (R : RED_LANG) (RS : RED_REF_SEM R).

  Module ST := RS.ST.
  Import R.
  Export ST.


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

End STAGED_REF_NATURAL_SEM.





Module Type REF_NATURAL_SEM (R : RED_LANG) (RS : RED_REF_SEM R).

  Module ST := RS.ST.
  Export ST.
  Import R.


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

End REF_NATURAL_SEM.





Module Type PE_REF_NATURAL_SEM (R : RED_LANG) (PERS : PE_RED_REF_SEM R).

  Module ST := PERS.ST.
  Export ST.
  Import R.


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
               ~ dead_ckind k ->
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

End PE_REF_NATURAL_SEM.





(*** Functors ***)


Require Import Util.
Require Export reduction_strategy.



Module PreRefNaturalSem (R : RED_LANG) (RS : RED_REF_SEM R) 
                                                <: PRE_REF_NATURAL_SEM R RS.

  Module ST := RS.ST.
  Export ST.
  Import R.


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

End PreRefNaturalSem.




Module StagedRefNaturalSem (R : RED_LANG) (RS : RED_REF_SEM R) 
                                                <: STAGED_REF_NATURAL_SEM R RS.

  Module ST := RS.ST.
  Import R.
  Export ST.


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

  Scheme dec_Ind    := Induction for dec    Sort Prop
    with decctx_Ind := Induction for decctx Sort Prop
    with iter_Ind   := Induction for iter   Sort Prop.


  Inductive eval : term -> value init_ckind -> Prop :=
  | e_intro : forall {t v}, dec t [.] v -> eval t v.

End StagedRefNaturalSem.




Module RefNaturalSem (R : RED_LANG) (RS : RED_REF_SEM R)
                                              <: REF_NATURAL_SEM R RS.

  Module ST := RS.ST.
  Export ST.
  Import R.


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

  Scheme dec_Ind    := Induction for dec    Sort Prop
    with decctx_Ind := Induction for decctx Sort Prop.


  Inductive eval : term -> value init_ckind -> Prop :=
  | e_intro : forall {t v}, dec t [.] v -> eval t v.

End RefNaturalSem.




Module PE_RefNaturalSem (R : RED_LANG) (PERS : PE_RED_REF_SEM R)
                                                  <: PE_REF_NATURAL_SEM R PERS.

  Module ST := PERS.ST.
  Export ST.
  Import R.


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
               ~ dead_ckind k ->
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

End PE_RefNaturalSem.


