(** * Definition of a 'coq-small' category *)

Record cat := catmk {
  ob : Type;
  hom : ob -> ob -> Type;
  id : forall a:ob, hom a a;
  comp : forall {a b c:ob}, hom a b -> hom b c -> hom a c;
  idl : forall a b (f : hom a b), comp (id a) f = f;
  idr : forall a b (f : hom a b), comp f (id b) = f;  
  compassoc : forall a b c d (f : hom a b) (g : hom b c) (h : hom c d),
    comp (comp f g) h = comp f (comp g h)
}.


(** Notations: [ f ; g = g ∘ f ] *)

Notation " f ;; g " := (comp _ f g) (at level 50).
Notation " a → b " := (hom _ a b) (at level 60).


(** Constructive [exists!] *)

Definition exuniq A P := sig (fun x : A =>
  P x /\ forall y, P y -> x = y).


(** Product and coproduct *)

Record product {C : cat} {A B : ob C} := {
  pair : ob C;
  p1 : pair → A;
  p2 : pair → B;
  product_ump :
    forall X (f : X → A) (g : X → B),
      exuniq (X → pair) (fun fg =>
        (fg ;; p1 = f /\ fg ;; p2 = g))
}.

Record coproduct {C : cat} {A B : ob C} := {
  union : ob C;
  i1 : A → union;
  i2 : B → union;
  coproduct_ump :
    forall X (f : A → X) (g : B → X),
      exuniq (union → X) (fun fg =>
        (i1 ;; fg = f /\ i2 ;; fg = g))
}.


(** Opposite category *)

Program Definition op : cat -> cat := fun C => {|
  ob := ob C;
  hom := fun a b => hom C b a;
  id := fun a => id C a;
  comp := fun a b c f g => comp C g f;
  idl := _;
  idr := _;
  compassoc := _
|}.
Next Obligation. intros. apply idr. Qed.
Next Obligation. intros. apply idl. Qed.
Next Obligation. intros. symmetry. apply compassoc. Qed.


(** Dump try-it-all tactic *)

Ltac catcons := intros;
  repeat
    (match goal with
    | p : prod _ _ |- _ => destruct p
    | p : unit |- _     => destruct p
    end; simpl in *);
  repeat (split || f_equal ||
    apply idl || apply idr || apply compassoc).


(** Product category *)

Program Definition prodcat : cat -> cat -> cat := fun C D => {|
  ob := ob C * ob D;
  hom := fun ab ab' =>
           let (a,b) := ab in
             let (a',b') := ab' in
               prod (hom C a a') (hom D b b')
|}.
Next Obligation. (* Definition of id (writing the term is awful) *)
  intros C D (a, b); simpl.
  exact (id C a, id D b).
Defined.
Next Obligation. (* Definition of the composition *)
  intros C D (a, a') (b, b') (c, c') (f, f') (g, g').
  exact (f ;; g, f' ;; g').
Defined.
(* proofs: we don't need to pay attention *)
Solve Obligations using catcons.


(** Isomorphic objects *)

Record isomorphic a b := isomorphicmk {
  isof : a → b;
  isog : b → a;
  isofg : isof ;; isog = id C a;
  isogf : isog ;; isof = id C b
}.


(** Products are unique up to iso *)

Lemma product_is_unique : forall a b (ab ab' : @product a b),
  isomorphic (pair ab) (pair ab').
Proof.
  intros a b ab ab'.
  destruct (product_ump ab' (pair ab) (p1 ab) (p2 ab)) as [f [[f1 f2] Uf]].
  destruct (product_ump ab (pair ab') (p1 ab') (p2 ab')) as [g [[g1 g2] Ug]].
  apply (isomorphicmk _ _ f g).
    destruct (product_ump ab (pair ab) (p1 ab) (p2 ab)) as [fg [[fg1 fg2] Ufg]].
    transitivity fg.
      symmetry.
      apply Ufg; split.
        rewrite compassoc.
        rewrite g1, f1.
        reflexivity.
        
        rewrite compassoc.
        rewrite g2, f2.
        reflexivity.
      
      apply Ufg; split.
        now apply idl.
        now apply idl.
    
    (* below, symmetrical proof, just shorter. *)
    destruct (product_ump ab' (pair ab') (p1 ab') (p2 ab')) as [gf [[gf1 gf2] Ugf]].
    transitivity gf.
      symmetry; apply Ugf; split; rewrite compassoc.
        rewrite f1, g1; now auto.
        rewrite f2, g2; now auto.
      apply Ugf; now catcons.
Qed.


(** Some finite categories *)

Program Definition one := {|
  ob := unit;
  hom := fun _ _ => unit;
  id := fun _ => tt;
  comp := fun _ _ _ _ _ => tt
|}.
Solve Obligations using (repeat (intros []); auto).

Program Definition two_without_arrow := {|
  ob := bool;
  hom := fun a b => if a then (if b then unit else False) else (if b then False else unit)
|}.
Next Obligation. repeat (intros []); exact tt. Defined.
Next Obligation. repeat (intros []); exact tt. Defined.
Solve Obligations using (repeat (intros []); simpl; auto).

Program Definition two_one_arrow := {|
  ob := bool;
  hom := fun a b => if a then (if b then unit else False) else (if b then unit else unit)
|}.
Next Obligation. repeat (intros []); exact tt. Defined.
Next Obligation. repeat (intros []); exact tt. Defined.
Solve Obligations using (repeat (intros []); simpl; auto).

Program Definition two_backandforth := {|
  ob := bool;
  hom := fun _ _ => unit;
  id := fun _ => tt;
  comp := fun _ _ _ _ _ => tt
|}.
Solve Obligations using (repeat (intros []); auto).


(** Functor *)

Record functor (C D : cat) := {
  Fo : ob C -> ob D;
  Fm : forall {a b}, hom C a b -> hom D (Fo a) (Fo b);
  F_id : forall a, Fm (id C a) = id D (Fo a);
  F_comp : forall a b c (f : a → b) (g : b → c), Fm (f ;; g) = (Fm f) ;; (Fm g)
}.


(** [Cat], the category of the [cat] categories, is a [cat']
category. First define a [cat'] category: *)

Record cat' := cat'mk {
  ob' : Type;
  hom' : ob' -> ob' -> Type;
  id' : forall a:ob', hom' a a;
  comp' : forall {a b c:ob'}, hom' a b -> hom' b c -> hom' a c;
  idl' : forall a b (f : hom' a b), comp' (id' a) f = f;
  idr' : forall a b (f : hom' a b), comp' f (id' b) = f;  
  compassoc' : forall a b c d (f : hom' a b) (g : hom' b c) (h : hom' c d),
    comp' (comp' f g) h = comp' f (comp' g h)
}.

(** Then the proofs (work in progress) *)

Program Definition Cat : cat' := {|
  ob' := cat;
  hom' := functor
|}.
Next Obligation. admit. Qed.
Next Obligation. admit. Qed.
Next Obligation. admit. Qed.
Next Obligation. admit. Qed. 

(*
Record exponentiation {A B : C} := {
  exp : Ob C;
  
}.*)