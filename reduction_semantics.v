Require Import Program.


(* Note: The only grammar mentioned in this formalization is a grammar of evaluation
   contexts, thus any reference to a grammar means the grammar of contexts of 
   the formalized language.
   
   In this formalisation we represent evaluation contexts in terms of elementary
   contexts (if you do not understand this go to the paper). To obtain the grammar 
   proper for this formalization first translate the original grammar to a form, 
   where each right side of a production is a hole or it has a context non-terminal.
   Now if you take each non-hole right side and replace the context symbol by a hole,
   you will a set of get context patterns that identify needed elementary contexts - 
   we will use EC markings for these patterns.

   E.g., if k1, k2 are context non-terminals and there is a production  k1 -> a b k2 c,
   then the coresponding context pattern is  a b [] c  .

   Unfortunatly, not all such grammars are proper for our formalisation, so we may 
   still need to refine them. If we try to say it intuitivly, the grammars describe 
   automata on words build from elementary contexts and these automata need to be 
   deterministic.

   Saying it less intuitvaly: for any context non-teminal symbol k and elem. context ec 
   there needs to be at most one k' such that there exists a production  k -> EC[k']  
   and ec matches EC. Let us call such grammars >deterministic grammars of contexts<. 

   You may achive this form by spliting the context patterns and determinizing 
   the grammar.

   E.g., suppose you have a grammar with two productions form k1:  k1 -> a k2 a,  
   k1 -> ab k3 ab,  where L(a), L(b) are disjoint languages and L(ab) = L(a) U L(b). 
   Then you may split the second pattern  ab [] ab  to:  a [] a,  b [] ab,  ab [] b. 
   So, the second production may be replaced by three other:  k1 -> a k3 a,  
   k -> b k3 ab,  k -> ab k3 b. And then you may determinize the grammar by the
   exponential construction. In this case, it will introduce a new context symbol 
   {k2,k3}, replacing the productions  k1 -> a k2 a,  k1 -> a k3 a  with  
   k1 -> a {k2,k3} a  and derivating the missing part of the grammar from the symbol
   {k2,k3}.

   In this formalisation contexts are treated as words of elementary contexts, where
   the end of a word means a hole. Because such a word may end in any place, this 
   enforces an additional condition on the grammars that, the production  k -> []  
   exists for any non-terminal k. However, this condition is not restrictive (keep
   reading).

   Definition: If a derivation of a context ends with a production  k -> [], then
   we say that the context has a >hole of the kind k<. 

   In this formalisation we may give a different set of redexes that may occure in 
   a hole per each hole kind. Hence, if there was no production  k -> [], then
   we may equivalently fix an empty set of redexes for this k. *)




(* Signature for languages with reduction semantics and multiple kinds of contextes. *)

Module Type RED_LANG.

  (* Preconditions: To instaniate this module you need to determinizethe grammar of 
     contextes. *)


  Parameters term  elem_context : Set.
  Parameter  ckind : Set. (* kinds of contexts, that is, non-terminal context symbols 
                             in the grammar *)


  Parameter  init_ckind : ckind.         (* start symbol in the grammar *)
  Parameter  dead_ckind : ckind -> Prop. (* set of sink symbols; if your grammar
                                            is not total you need to introduce at least
                                            one *)


  (* ckind_trans - function that determinates the productions in the grammar, that is,
                   if ckind_trans k1 ec = k2, then k1 -> EC[k2] where ec matches EC or
                   there is no such production and k2 is a sink. 
                   In other words, it is the transition function of a finit automaton 
                   representing the totalized grammar. *)
  Parameter  ckind_trans : ckind -> elem_context -> ckind.
  Infix "+>" := ckind_trans (at level 50, left associativity).


  (* The sink property: *)
  Axiom death_propagation : 
      forall k, dead_ckind k -> forall ec, dead_ckind (k+>ec).



  (* context k1 k2 - contexts of kind k1 (derivated from k1) with a hole of kind k2. 
                     Contexts are represented by reversed derivations in the grammar.
                     E.g., if a context is derivated by a sequence of productions
                     k1 -> ec1 k2, k2 -> ec2 k3, k3 -> ec3 k4, k4 -> [], then it is 
                     represented by the list  (ec3, k4), (ec2, k3), (ec1, k2)  ot 
                     the type  context k1 k4.
                     The second elements in the pairs are implicite. *)
  Inductive context (k1 : ckind) : ckind -> Set :=
  | empty : context k1 k1
  | ccons : forall (ec : elem_context) {k2}, context k1 k2 -> context k1 (k2+>ec).
  Arguments empty {k1}. Arguments ccons {k1} _ {k2} _.

  Notation "[.]"      := empty.
  Notation "[.]( k )" := (@empty k).
  Infix    "=:"       := ccons (at level 60, right associativity).

  (* Note: Contexts are reversed, because during evaluation by refocusing we always 
     access the elem. context nearest to the hole of a context. *)


  (* Definition: The hole of a context is >dead< if its kind is a sink symbol. *)

  (* Definition: A context is >proper< if its hole is not dead. 
     (Context with dead holes are contexts that cannot be generated in the orginal
     grammar.) *)



  (* Plugging is standard. You need to provide only plugging function for elem.
     contexts. *)

  Parameter elem_plug : term -> elem_context -> term.
  Notation "ec :[ t ]" := (elem_plug t ec) (at level 0, t at level 99).

  Fixpoint plug (t : term) {k1 k2} (c : context k1 k2) : term :=
      match c with
      | [.]    => t 
      | ec=:c' => plug ec:[t] c'
      end.
  Notation "c [ t ]" := (plug t c) (at level 0, t at level 99).

  (* The following axiom, somehow, relates our representation of contexts to the 
     real eval. contexts, but generally we can instantiate the module with 
     elem. contexts that do not represent real elem. contexts and so not
     every module of this signature is a proper. *)
  Axiom elem_plug_injective1 : forall ec {t0 t1}, ec:[t0] = ec:[t1] -> t0 = t1.


  (* An intuitive definition: *)
  Definition immediate_ec ec t := exists t', ec:[t'] = t.



  (* redex k - representations of redexes that may occur in a hole of the kind k. 
     value k where k is not a sink
             - (almost) normal forms of kind k, that is, representations of terms
               that cannot be decomposed to a context k k' and a redex k'.  value k
               where k is a sink may be anything. *)
  Parameters value redex : ckind -> Set.


  Parameter value_to_term : forall {k}, value k -> term.
  Coercion  value_to_term : value >-> term.
  Parameter redex_to_term : forall {k}, redex k -> term.
  Coercion  redex_to_term : redex >-> term.

  Axiom value_to_term_injective : 
      forall {k} (v v' : value k), value_to_term v = value_to_term v' -> v = v'.
  Axiom redex_to_term_injective : 
      forall {k} (r r' : redex k), redex_to_term r = redex_to_term r' -> r = r'.


  (* A key property of sink non-terminals: *)
  Axiom proper_death : forall k1, dead_ckind k1 -> 
                           ~ exists k2 (c : context k1 k2) (r : redex k2), True.


  (* Definition: A decomposition c[t] is empty if c is empty. *)
  (* Definition: A decomposition c[t] is proper if c is proper. *)

  (* only_empty t k   - the term t has only empty or improper decompositions from 
                        the symbol k.
     only_trivial t k - each proper decomposition of the term t from the symbol k is 
                        either empty or the component term is a value. *)
  Definition only_empty t k :=
      forall t' {k'} (c : context k k'), c[t'] = t -> ~ dead_ckind k' -> 
          k = k' /\ c ~= [.](k).
  Definition only_trivial t k :=
      forall t' {k'} (c : context k k'), c[t'] = t -> ~ dead_ckind k' -> 
          k = k' /\ c ~= [.](k) \/ exists (v : value k'), t' = v.


  (* Axioms of normal forms: *)
  Axiom value_trivial : forall {k} (v : value k), only_trivial v k.
  Axiom value_redex   : forall {k} (v : value k) (r : redex k), 
                            value_to_term v <> redex_to_term r.
  Axiom trivial_val_red : 
      forall k t, only_trivial t k ->
         (exists (v : value k), t = v) \/ (exists (r : redex k), t = r).



  (* Reduction of a redex (it may get stuck): *)
  Parameter contract : forall {k}, redex k -> option term.



  (* decomp k  - decomposition of a term t from the symbol k to a redex.
     d_red r c  means: t = c[r].
     d_val v    means: t has no redexes and so it is a value, t = v. *)
  Inductive decomp k : Set :=
  | d_red : forall {k'}, redex k' -> context k k' -> decomp k
  | d_val : value k -> decomp k.
  Arguments d_val {k} _. Arguments d_red {k} {k'} _ _.

  Definition decomp_to_term {k} (d : decomp k) :=
      match d with
      | d_val v     => value_to_term v
      | d_red _ r c => c[r]
      end.
  Coercion decomp_to_term : decomp >-> term.



  (* Standard contexts composition: *)
  Fixpoint compose {k1 k2} (c0 : context k1 k2) 
                      {k3} (c1 : context k3 k1) : context k3 k2 := 
      match c0 in context _ k2' return context k3 k2' with
      | [.]     => c1
      | ec=:c0' => ec =: compose c0' c1
      end.
  Infix "~+" := compose (at level 60, right associativity).

End RED_LANG.




(* Signature for reduction semantics *)

Module Type RED_SEM (R : RED_LANG).

  Import R.


  (* This is a property of the language and should be in RED_LANG, but doing so
     overcomplicate the library, thus we leave it here for now. *)
  Axiom decompose : forall (t : term) k1, ~ dead_ckind k1 ->
      (exists (v : value k1), t = v) \/
      (exists k2 (r : redex k2) (c : context k1 k2), t = c[r]).


  (* Decomposition relation 
     dec t c d - the term c[t] can be decomposed to d. *)
  Parameter dec : 
      term -> forall {k1 k2}, context k1 k2 -> decomp k1 -> Prop.

  Axiom dec_correct  : forall {t k1 k2} {c : context k1 k2} {d}, 
                           dec t c d -> c[t] = d.


  (* Following two axioms say that  dec t c d  is equivalnet to  dec c[t] [.] d. *)
  Axiom dec_plug : 
      forall {k1 k2} (c : context k1 k2) {k3} {c0 : context k3 k1} {t d}, 
          ~ dead_ckind k2 -> dec c[t] c0 d -> dec t (c ~+ c0) d.

  Axiom dec_plug_rev : 
      forall {k1 k2} (c : context k1 k2) {k3} {c0 : context k3 k1} {t d}, 
          ~ dead_ckind k2 -> dec t (c ~+ c0) d -> dec c[t] c0 d.



  (* Together with the previous axioms this ensures that dec contains every 
     decomposition to a redex. (We care only about non-dead k2, but this is 
     implied by the existance of a redex k2.) *)
  Axiom dec_redex_self : forall {k2} (r : redex k2) {k1} (c : context k1 k2), 
                             dec r c (d_red r c).

  (* All proper values need to be in dec. *)
  Axiom dec_value_self : forall {k} (v : value k), 
                             ~ dead_ckind k -> dec v [.] (d_val v).


  (* Decomposition of a term *)
  Inductive decempty : term -> forall {k}, decomp k -> Prop :=
  | d_intro : forall {t k} {d : decomp k}, dec t [.] d -> decempty t d.

  (* An evaluation process - starting from a "decomp" *)
  Inductive iter : forall {k}, decomp k -> value k -> Prop :=
  | i_val : forall {k} (v : value k), iter (d_val v) v
  | i_red : forall {k2} (r : redex k2) {t k1} (c : context k1 k2) {d v},
                contract r = Some t -> decempty c[t] d -> iter d v ->
                iter (d_red r c) v.

  (* An effective evaluation process - starting from a term *)
  Inductive eval : term -> value init_ckind -> Prop :=
  | e_intro : forall {t} {d : decomp init_ckind} {v : value init_ckind}, 
                  decempty t d -> iter d v -> eval t v.

End RED_SEM.




(* Signature for deterministic reduction semantics *)

Module Type DET_RED_SEM (R : RED_LANG).

  Declare Module RS : RED_SEM R.

  Import R.
  Export RS.


  Axiom dec_is_function  : forall {t k} {d d0 : decomp k}, 
                               decempty t d -> decempty t d0 -> d = d0.
  Axiom iter_is_function : forall {k} {d : decomp k} {v v0}, 
                               iter d v -> iter d v0 -> v = v0.
  Axiom eval_is_function : forall {t} {v v0 : value init_ckind}, 
                               eval t v -> eval t v0 -> v = v0.

End DET_RED_SEM.

