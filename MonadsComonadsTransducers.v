Require Import Logic.FunctionalExtensionality.
Require Import Coq.Program.Basics.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.Morphisms.

Notation " g * f " := (compose g f)
  (at level 40, left associativity) : program_scope.



Open Scope program_scope.


(*We start with some notation of Cartesian Closed Categories*)
Definition proj1 {A B} (x : A * B) : A :=
  match x with 
    (x1, x2) => x1
  end.

Definition proj2 {A B} (x : A * B) : B :=
  match x with 
    (x1, x2) => x2
  end.

Definition app {A} {B} (f : A -> B) (x : A) : B := 
  f x.

Definition app2 {A} {B} (x : (A -> B) * A) := 
  match x with 
    (f, x) => f x
  end.

Definition pairing {A B C} (f : A -> B) (g : A -> C) (x : A) : (B * C) :=
  (f x, g x).

Notation " <| f , g |> " := (pairing f g)
  (at level 40, no associativity).

Definition func_prod { A B C D} (f : A -> B) (g : C -> D) (x : A * C) : (B * D) := 
  match x with 
    | (x1, x2) => (f x1, g x2)
  end.

Notation " <* f , g *> " := (func_prod f g)
  (at level 40, no associativity).



(*We are given a functor M*)
Parameter M : Type -> Type.
Parameter mapM : forall {A} {B}, (A -> B) -> M A -> M B.

Notation " # f " := (mapM f)
  (at level 39, left associativity).

(*mapM satisfied functor axioms*)

Axiom mapCompose : forall {A} {B} {C} (f : B -> C) (g : A -> B) (mx : M A),
  (#f)((#g) mx) = (#(compose f g)) mx.

Axiom mapId : forall {A} (x : M A), 
  (# id) x = x.

(*M is a monad*)

Parameter mult : forall {A}, M (M A) -> M A.
Parameter unit : forall {A}, A -> M A.

(*Monad operations are natural*)

Axiom multNatural : forall A B, forall f : A -> B, forall x,
  mult((#(#f)) x) = (#f)(mult x).

Axiom unitNatural : forall A B, forall f : A -> B, forall x,
  unit(f x) = (#f)(unit x).

(*Monad operations satisfy monad axioms*)
Axiom multAx : forall A (x : M (M (M A))), 
  mult (mult x) = mult ((#mult) x).

Axiom multMapUnitAx : forall A (x : M A), 
  mult ((# unit) x) = x.

Axiom multUnitAx : forall A (x : M A),
  mult (unit x) = x.

(*M is a comonad*)

Parameter coMult : forall {A}, M A -> (M (M A)).
Parameter coUnit : forall {A}, M A -> A.

(*Comonad operations are natural*)
Axiom coUnitNatural : forall A B, forall f : A -> B, forall x,
  f (coUnit x) = (coUnit ((#f) x)).

Axiom coMultNatural : forall A B, forall f : A -> B, forall m,
  coMult ((#f) m) = (#(#f)) (coMult m).

(*Comonad operations satisfy comonad axioms*)
Axiom coMultAx : forall A (x : M A),
  coMult (coMult x) = (#coMult) (coMult x).

Axiom coUnitCoMultAx : forall A (x : M A),
  coUnit (coMult x) = x.

Axiom mapCoUnitComultAx : forall A (x : M A),
  (#coUnit) (coMult x) = x.

(*M implements a put opearation, i.e. putting a new element in place of the the focused element*)

Parameter put : forall {A},  ((M A) * A) -> M A.

(*Put is natural*)
Axiom putNatural : forall {A} {B} (f : A -> B) (xs : M A) (x : A),
  (#f) (put (xs, x)) = put ((#f) xs, f x).



(*M has strenght*)
(*For now, we implement the strenght, but the further plan is to make it more abstract*)


(*Cross structure coherence axioms*)

Axiom flattenExtract : forall A, forall (x : M (M A)),
  coUnit (mult x) = coUnit (coUnit x).

Axiom singletonExpand : forall A, forall (x : A), 
  coMult (unit x) = (#unit) (unit x).

Axiom singletonExtract : forall A, forall (x : A), 
  coUnit (unit x) = x.

Axiom getPut : forall A, forall (x : M A) (y : A),
  coUnit (put (x, y)) = y.

Axiom putGet : forall A, forall (x : M A), 
  put (x, coUnit x) = x.

Axiom putPut : forall {A} l (x : A) y, 
  put (put(l, x), y) = put (l, y).

Axiom putAssoc : forall A, forall (x : M (M A)) (y: M A) (z : A),
   put ((mult (put (x, y))), z) = mult (put (x, put (y, z))).

Axiom singletonPut : forall A (x : A) y, 
  put(unit x, y) = unit y. 

(*The Set-specific definition of strength*)
Definition str {X} {Y} (x : X * (M Y)) : (M (X*Y)) := 
  match x with 
    (x1, x2) => (#(fun y => (x1, y))) x2
  end.

Axiom flattenExpand : forall {A} (x : M (M A)),
  coMult (mult x) = 
  mult ( (#(# mult)) ( ((#(#put)) ((# str) ((#<| id, coMult * coUnit|>) (coMult x)))))).


(*An M-algebra is a pair (S, M S -> S) that satisfies the associativity axiom*)
Definition associative {S} (prod : M S -> S) : Prop := 
  forall l,  prod ((#prod) l) = prod (mult l).

Definition unitInvariant {S} (prod : M S -> S) : Prop := 
  forall s, prod (unit s) = s.


(*Now we can use an M-algebra to define na M-transduction of type X -> Y*)
(*An M-transdcutions is defined by:
  1) a M-algebra (S, prod);
  2) an input function (h : X -> S)
  3) an output function (lambda : S -> Y) *)
Definition mTransduction {X Y S} (prod : M S -> S) (h : X -> S) (lambda : S -> Y) : M X -> M Y := 
   (#lambda) * (#prod) * coMult * (#h).

(*If S is an actual M-algebra (i.e. it is associative) and S is finite, 
  mTransdcutions define a class of regular transdcutions. 
  For example, if M is the non-empty list + preffixes, 
  the mTransdcutions are Mealy machines*)

Section contexts.

Variable S : Set.
Variable prod : M S -> S. 
Axiom prodAssoc : associative prod.
Axiom prodUnit : unitInvariant prod.

Definition ctx (l : M S) (x : S) : S := 
  prod (put (l, x)).

Lemma ctxPutInvariant : forall l a, ctx l = ctx (put (l, a)).
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold ctx.
  rewrite putPut.
  reflexivity.
Qed.

Lemma ctxUnitId : forall x, ctx (unit x) = id.
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold ctx.
  rewrite singletonPut.
  rewrite prodUnit.
  reflexivity.
Qed.

Definition concat : M S * M S -> M S := 
  mult * put * <* (#unit), id *>.

Lemma concatCtx : forall (v w : M S), 
  ctx v * ctx w = ctx (concat (v, w)).
Proof.
  intros.
  unfold ctx.
  unfold concat.
  apply functional_extensionality.
  unfold compose.
  intros.
  simpl.
  rewrite putAssoc.
  unfold id.
  rewrite <- prodAssoc.
  rewrite putNatural.
  rewrite mapCompose.
  unfold compose.
  replace (fun x0 : S => prod (unit x0)) with (@id S)
  by (apply functional_extensionality; intros; rewrite prodUnit; reflexivity).
  rewrite mapId.
  reflexivity.
Qed.

End contexts.

Section compositions.
(*In this section The main result that we want to proof is that M-transdcutions are closed under compositions*)

(*We are given three prodbets *)
Variable X : Set.
Variable Y : Set.
Variable Z : Set.

(*We are given and M-transduction F :  M X -> M Y*)
Variable S1 : Set.
Variable prod1 : M S1 -> S1.
Variable h1 : X -> S1.
Variable lambda1 : S1 -> Y.
Axiom assoc1 : associative prod1.
Axiom unitInvariant1 : unitInvariant prod1.
Definition F := mTransduction prod1 h1 lambda1.

(*And we are given an M-transduction G : MY -> M Z*)
Variable S2 : Set.
Variable prod2 : M S2 -> S2.
Variable h2 : Y -> S2.
Variable lambda2 : S2 -> Z.
Axiom assoc2 : associative prod2.
Axiom unitInvariant2 : unitInvariant prod2.
Definition G := mTransduction prod2 h2 lambda2.



(*Now we define an S3, h3, lambda3*)

Definition S3 : Type := S1 * ((S1 -> S1) -> S2).
Definition prod3 (l : M S3) : S3 :=
  let ctx1 (l : M S1) (x : S1) : S1 := prod1 (put (l, x)) in 
  let tmp1 (l : M S3) : ((S1 -> S1) -> S2) := proj2 (coUnit l) in 
  let tmp2 (c : S1 -> S1) (l : M S3) : (S1 -> S1) := c * (ctx1 ((#proj1)(l))) in 
  (prod1 ((#proj1) (l)), fun c => prod2 ( (#app2) (((#<|tmp1, tmp2 c |>) (coMult l))))).

Definition h3 (x : X) : S3 := 
  (h1 x, fun c => h2 (lambda1 (c (h1 x)))).

Definition lambda3 (s : S3) : Z :=
  match s with 
    | (_, f) => lambda2 (f (fun a => a))
  end.

Definition GF := mTransduction prod3 h3 lambda3.

Theorem compositionCorrect : GF = G * F.
Proof.
  apply functional_extensionality.
  intros. unfold compose.
  unfold GF. unfold G. unfold F.
  unfold mTransduction. unfold compose.
  unfold lambda3. unfold prod3.
  unfold h3. repeat rewrite mapCompose.
  unfold compose. unfold pairing.
  unfold proj1. unfold proj2.
  simpl. unfold app2.
  rewrite coMultNatural.
  repeat rewrite mapCompose.
  unfold compose.
  rewrite coMultNatural.
  repeat rewrite mapCompose.
  unfold compose.
  repeat rewrite coMultNatural.
  repeat rewrite mapCompose.
  unfold compose.
  replace (fun x0 : M (M X) => lambda2 (prod2 ((# (fun x1 : M S1 => h2 (lambda1 (prod1 x1)))) ((# (# h1)) x0))))
  with (fun x0 => lambda2 (prod2 ((# (fun x1 : M X => h2 (lambda1 (prod1 ((# h1) x1))))) x0)))
  by (apply functional_extensionality; intros; repeat rewrite mapCompose; unfold compose; reflexivity).
  assert (
    (fun x0 : M X =>
    lambda2
      (prod2
         ((# (fun x1 : ((S1 -> S1) -> S2) * (S1 -> S1) => let (f, x2) := x1 in f x2))
            ((# (fun x1 : M S3 =>
                 (let (_, x3) := coUnit x1 in x3,
                 fun x2 : S1 =>
                 prod1
                   (put ((# (fun x3 : S1 * ((S1 -> S1) -> S2) => let (x4, _) := x3 in x4)) x1, x2)))))
               (coMult
                  ((# (fun x1 : X => (h1 x1, fun c : S1 -> S1 => h2 (lambda1 (c (h1 x1)))))) x0))))))
    =
    (fun x0 => lambda2 (prod2 ((# (fun x1 : M X => h2 (lambda1 (prod1 ((# h1) x1))))) (coMult x0))))
  ) as eq.
  {
    apply functional_extensionality.
    intros.  rewrite coMultNatural.
    repeat rewrite mapCompose.
    unfold compose.
    assert (
    (fun x1 : M X =>
          (let (_, x3) :=
             coUnit ((# (fun x2 : X => (h1 x2, fun c : S1 -> S1 => h2 (lambda1 (c (h1 x2)))))) x1) in
           x3)
            (fun x2 : S1 =>
             prod1
               (put
                  ((# (fun x3 : S1 * ((S1 -> S1) -> S2) => let (x4, _) := x3 in x4))
                     ((# (fun x3 : X => (h1 x3, fun c : S1 -> S1 => h2 (lambda1 (c (h1 x3)))))) x1),
                  x2)))) = 
    (fun x1 => h2 (lambda1 (prod1 ((# h1) x1)))))
    as eq2.
    { apply functional_extensionality. intros. 
      rewrite <- coUnitNatural.
      repeat rewrite mapCompose. unfold compose.
      replace (fun x2 : X => h1 x2) with h1 by (apply functional_extensionality; intros; reflexivity).
      rewrite <- putNatural.
      rewrite putGet.
      reflexivity.
    }
    unfold S3 in *.
    rewrite eq2.
    reflexivity.
  }
  unfold S3 in *.
  rewrite eq.
  rewrite coMultAx.
  repeat rewrite mapCompose.
  unfold compose.
  reflexivity.
Qed.


 
(*An auxiliarry lemma for s3assoc. It has not meanining on its own, 
and is only required to be a separeate lemma for some technical reasons*)
Lemma s3assoc2aux : forall x, 
((fun x0 : M (M S3) =>
       proj2
         (coUnit
            ((# (fun l0 : M S3 =>
                 (prod1 ((# proj1) l0),
                 fun c : S1 -> S1 =>
                 prod2
                   ((# (fun x1 : ((S1 -> S1) -> S2) * (S1 -> S1) => let (f, x2) := x1 in f x2))
                      ((# (fun x1 : M S3 =>
                           (proj2 (coUnit x1), fun x2 : S1 => c (prod1 (put ((# proj1) x1, x2))))))
                         (coMult l0)))))) x0))
         (fun x1 : S1 =>
          x
            (prod1
               (put
                  ((# proj1)
                     ((# (fun l0 : M S3 =>
                          (prod1 ((# proj1) l0),
                          fun c : S1 -> S1 =>
                          prod2
                            ((# (fun x2 : ((S1 -> S1) -> S2) * (S1 -> S1) =>
                                 let (f, x3) := x2 in f x3))
                               ((# (fun x2 : M S3 =>
                                    (proj2 (coUnit x2),
                                    fun x3 : S1 => c (prod1 (put ((# proj1) x2, x3)))))) 
                                  (coMult l0)))))) x0), x1)))))) = 
((fun x0 : M (M S3) =>
      prod2
  ((# (fun x3 : M S3 =>
       proj2 (coUnit x3)
         (fun x4 : S1 =>
          x
            (prod1
               (put ((# (fun x1 : M S3 => prod1 ((# proj1) x1))) x0, prod1 (put ((# proj1) x3, x4))))))))
     (coMult (coUnit x0))))).
Proof.
  intros. 
  apply functional_extensionality.
  intros. repeat rewrite coUnitNatural.
  repeat rewrite mapCompose.
  unfold compose. unfold proj2 at 1.
  unfold proj1 at 2.
  replace (fun (x1 : M S3) (c : S1 -> S1) =>
       prod2
         ((# (fun x2 : ((S1 -> S1) -> S2) * (S1 -> S1) => let (f, x3) := x2 in f x3))
            ((# (fun x2 : M S3 =>
                 (proj2 (coUnit x2), fun x3 : S1 => c (prod1 (put ((# proj1) x2, x3))))))
               (coMult x1))))
  with (fun (x1 : M S3) (c : S1 -> S1) =>
          prod2
  ((# (fun x3 : M S3 => proj2 (coUnit x3) (fun x4 : S1 => c (prod1 (put ((# proj1) x3, x4))))))
     (coMult x1)))
  by (apply functional_extensionality; intros; apply functional_extensionality;
      intros; repeat rewrite mapCompose; unfold compose; reflexivity;  simpl).
  repeat rewrite <- coUnitNatural.
  replace (fun x1 : M S3 => prod1 ((# proj1) x1))
  with (prod1 * (fun x1 : M S3 => ((# proj1) x1))) 
  by reflexivity.
  rewrite <- mapCompose.
  replace (fun x3 : M S3 =>
       proj2 (coUnit x3)
         (fun x4 : S1 =>
          x
            (prod1
               (put
                  ((# prod1) ((# (fun x1 : M S3 => (# proj1) x1)) x0),
                  prod1 (put ((# proj1) x3, x4)))))))
  with (fun x3 : M S3 =>
       proj2 (coUnit x3) (fun x4 : S1 => x (prod1 (put ((# proj1) (mult (put (x0, x3))), x4)))))
  by

  (apply functional_extensionality;
  intros x3;
  replace (fun x4 : S1 =>
   x
     (prod1
        (put ((# prod1) ((# (fun x2 : M S3 => (# proj1) x2)) x0), prod1 (put ((# proj1) x3, x4))))))
  with (fun x4 : S1 =>
     x (prod1 (put ((# proj1) (mult (put (x0, x3))), x4))))
  by
  (apply functional_extensionality; intros x4; rewrite <- putNatural; rewrite assoc1;
  rewrite <- putAssoc;
  replace ((fun x2 : M S3 => (# proj1) x2)) with (# (@proj1 S1 ((S1 -> S1) -> S2))) by (apply functional_extensionality; intros; reflexivity);
  rewrite <- putNatural; rewrite multNatural; reflexivity);
  reflexivity).
  reflexivity.
Qed.





Theorem s3assoc2 : forall l, 
  prod3 (mult l) = prod3 ((#prod3) l).
Proof.
  intros.
  unfold prod3.
  apply pair_equal_spec. split.
  { unfold pairing.
  rewrite <- multNatural. unfold app2.
  unfold compose.
  repeat rewrite mapCompose.
  unfold compose.
  unfold proj1.
  rewrite <- assoc1.
  repeat rewrite mapCompose. 
  unfold compose. reflexivity.
  }
  unfold pairing.
  apply functional_extensionality.
  intros.
  repeat rewrite mapCompose. 
  unfold app2.
  unfold compose.
  rewrite flattenExpand.
  unfold pairing. 
  unfold compose.
  unfold id.
  repeat rewrite mapCompose.
  unfold compose.
  simpl.
  (*unfold put.*)
  rewrite coMultNatural.
  repeat rewrite mapCompose.
  unfold compose.
  
  rewrite s3assoc2aux.
  replace  (fun x0 : M (M S3) =>
       prod2
         ((# (fun x3 : M S3 =>
              proj2 (coUnit x3)
                (fun x4 : S1 =>
                 x
                   (prod1
                      (put
                         ((# (fun x1 : M S3 => prod1 ((# proj1) x1))) x0,
                         prod1 (put ((# proj1) x3, x4)))))))) (coMult (coUnit x0))))
  with
     (prod2 * (fun x0 : M (M S3) =>
         ((# (fun x3 : M S3 =>
              proj2 (coUnit x3)
                (fun x4 : S1 =>
                 x
                   (prod1
                      (put
                         ((# (fun x1 : M S3 => prod1 ((# proj1) x1))) x0,
                         prod1 (put ((# proj1) x3, x4)))))))) (coMult (coUnit x0)))))
  by reflexivity.
  rewrite <- mapCompose.
  rewrite assoc2.
  replace (fun x0 : M (M S3) =>
             (# mult) ((# put) ((# (fun y : M S3 => (x0, y))) (coMult (coUnit x0)))))
  with 
          ((fun x0 : M (M S3) => (# (fun x1 : M S3 => mult (put (x0, x1)))) (coMult (coUnit x0))))
  by (apply functional_extensionality; intros; repeat rewrite mapCompose; reflexivity).
  rewrite <- multNatural.
  repeat rewrite mapCompose. unfold compose.
  repeat rewrite mapCompose.
  replace 
  (fun x0 : M (M S3) =>
          (# (fun x1 : M S3 => proj2 (coUnit x1) (fun x2 : S1 => x (prod1 (put ((# proj1) x1, x2))))))
            ((# (fun x1 : M S3 => mult (put (x0, x1)))) (coMult (coUnit x0))))
  with (fun x0 : M (M S3) =>
         (# (fun x3 : M S3 =>
    proj2 (coUnit (mult (put (x0, x3))))
      (fun x4 : S1 => x (prod1 (put ((# proj1) (mult (put (x0, x3))), x4)))))) 
  (coMult (coUnit x0))) by
  (apply functional_extensionality; intros;
  rewrite mapCompose; unfold compose; reflexivity).
  replace (fun x0 : M (M S3) =>
          (# (fun x3 : M S3 =>
              proj2 (coUnit x3)
                (fun x4 : S1 =>
                 x
                   (prod1
                      (put
                         ((# (fun x1 : M S3 => prod1 ((# proj1) x1))) x0,
                         prod1 (put ((# proj1) x3, x4)))))))) (coMult (coUnit x0)))
  with (fun x0 : M (M S3) =>
       (# (fun x3 : M S3 =>
    proj2 (coUnit x3)
      (fun x4 : S1 => x (prod1 ((# prod1) (put ((# (# proj1)) x0, put ((# proj1) x3, x4))))))))
  (coMult (coUnit x0)))
  by
  (apply functional_extensionality; intros;
  (replace (fun x3 : M S3 =>
    proj2 (coUnit x3)
      (fun x4 : S1 =>
       x
         (prod1
            (put ((# (fun x1 : M S3 => prod1 ((# proj1) x1))) x0, prod1 (put ((# proj1) x3, x4)))))))
  with (fun x3 : M S3 =>
    proj2 (coUnit x3)
      (fun x4 : S1 => x (prod1 ((# prod1) (put ((# (# proj1)) x0, put ((# proj1) x3, x4)))))))
  by
  (apply functional_extensionality;
  intros x3;
  replace (fun x1 : M S3 => prod1 ((# proj1) x1)) with (prod1 * (fun x1 : M S3 =>  ((# proj1) x1))) by reflexivity;
  rewrite <- mapCompose;
  replace  (fun x4 : S1 =>
   x
     (prod1
        (put ((# prod1) ((# (fun x1 : M S3 => (# proj1) x1)) x0), prod1 (put ((# proj1) x3, x4))))))
  with  (fun x4 : S1 =>
    x (prod1 ((# prod1) (put ((# (# proj1)) x0, put ((# proj1) x3, x4))))))
  by
  (apply functional_extensionality; intros x4;
  rewrite <- putNatural;
  replace (fun x1 : M S3 => (# proj1) x1) with (#(@proj1 S1 ((S1->S1)->S2))) by
  (apply functional_extensionality; intros; reflexivity);
  reflexivity);
  reflexivity));
  reflexivity).
  repeat rewrite <- mapCompose.
  simpl.
  replace ((fun x0 : M (M S3) =>
          (# (fun x3 : M S3 =>
              proj2 (coUnit (mult (put (x0, x3))))
                (fun x4 : S1 => x (prod1 (put ((# proj1) (mult (put (x0, x3))), x4))))))
            (coMult (coUnit x0))))
  with (fun x0 : M (M S3) =>
          (# (fun x3 : M S3 =>
    proj2 (coUnit x3) (fun x4 : S1 => x (prod1 (put ((# proj1) (mult (put (x0, x3))), x4))))))
  (coMult (coUnit x0))) by
  (
  apply functional_extensionality;
  intros;
  replace ((fun x3 : M S3 =>
    proj2 (coUnit (mult (put (x0, x3))))
      (fun x4 : S1 => x (prod1 (put ((# proj1) (mult (put (x0, x3))), x4))))))
  with ((fun x3 : M S3 =>
    proj2 (coUnit x3) (fun x4 : S1 => x (prod1 (put ((# proj1) (mult (put (x0, x3))), x4))))))
  by
  (apply functional_extensionality;
  intros x3;
  rewrite flattenExtract;
  rewrite getPut;
  reflexivity);
  reflexivity).
  replace (fun x0 : M (M S3) =>
          (# (fun x3 : M S3 =>
              proj2 (coUnit x3)
                (fun x4 : S1 =>
                 x (prod1 ((# prod1) (put ((# (# proj1)) x0, put ((# proj1) x3, x4))))))))
            (coMult (coUnit x0)))
  with 
  (fun x0 : M (M S3) =>
         (# (fun x3 : M S3 =>
    proj2 (coUnit x3) (fun x4 : S1 => x (prod1 (put ((# proj1) (mult (put (x0, x3))), x4))))))
  (coMult (coUnit x0))) by
 
  (apply functional_extensionality;
  intros x0;
  replace (fun x3 : M S3 =>
    proj2 (coUnit x3)
      (fun x4 : S1 => x (prod1 ((# prod1) (put ((# (# proj1)) x0, put ((# proj1) x3, x4)))))))
  with (fun x3 : M S3 =>
    proj2 (coUnit x3) (fun x4 : S1 => x (prod1 (put ((# proj1) (mult (put (x0, x3))), x4)))))
  by
  (apply functional_extensionality; intros x3;
  replace (fun x4 : S1 => x (prod1 ((# prod1) (put ((# (# proj1)) x0, put ((# proj1) x3, x4))))))
  with (fun x4 : S1 => x (prod1 (put ((# proj1) (mult (put (x0, x3))), x4))))
  by
  (apply functional_extensionality;
  intros x4;
  rewrite assoc1;
  rewrite <- putAssoc;
  rewrite <- putNatural;
  rewrite multNatural;
  reflexivity);
  reflexivity);
  reflexivity).
  reflexivity.
Qed.

Theorem S3Associative : associative prod3.
Proof.
  unfold associative.
  intros.
  rewrite s3assoc2.
  reflexivity.
Qed.

Lemma S3UnitInvariantAux : forall (x : S1 -> S1) (s : S1) (s0  : (S1 -> S1) -> S2),
(fun x0 : S1 => x (prod1 (put ((# proj1) (unit (s, s0)), x0)))) = x.
Proof. 
  intros. apply functional_extensionality. intros.
  rewrite <- unitNatural.
  simpl. rewrite singletonPut.
  rewrite unitInvariant1.
  reflexivity.
Qed.

Theorem S3UnitInvariant : unitInvariant prod3. 
Proof.
  unfold unitInvariant.
  unfold prod3.
  intros.
  destruct s.
  apply pair_equal_spec. split.
  + rewrite <- unitNatural.
    unfold proj1. simpl.
    apply unitInvariant1.
  + apply functional_extensionality.
    intros. 
    rewrite mapCompose.
    unfold compose.
    simpl. 
    rewrite singletonExpand.
    rewrite mapCompose.
    rewrite <- unitNatural.
    unfold compose.
    rewrite unitInvariant2.
    rewrite singletonExtract.
    rewrite S3UnitInvariantAux.
    reflexivity.
Qed.
    
End compositions.


Section identity.

(*Now we show that iddenty is always a M-transduction *)


Variable X : Set.

(*Our algebra with identity is (X, coUnit)*)

Definition SId := X.
Definition prodId : M X -> X := coUnit.
Definition hId : X -> X := id.
Definition lambdaId : X -> X := id.
Definition transId := mTransduction prodId hId lambdaId.

Theorem transIdCorrect : transId = id.
Proof.
  unfold transId.
  unfold mTransduction.
  unfold lambdaId.
  unfold hId.
  apply functional_extensionality. intros.
  unfold compose.
  repeat rewrite mapId.
  unfold prodId.
  rewrite mapCoUnitComultAx.
  reflexivity.
Qed.

Theorem prodIdAssoc : associative prodId.
Proof.
  unfold associative. unfold prodId.
  intros. rewrite flattenExtract.
  rewrite <- coUnitNatural.
  reflexivity.
Qed.
 
End identity.

Section alternativeDefinition.
(*  Here we show an equivalent implementation of the 5th coherence axiom *)
(*  It states that M A with mult and coMult is an bialgebra*)

(* Links to diagrams*)
(*https://q.uiver.app/#q=WzAsOSxbMCwyLCJNIE0gWCJdLFs2LDMsIk0gWCJdLFsxLDAsIk0gTSBNIFgiXSxbMywwLCJNIE0gTSBNIFgiXSxbNSwwLCJNIChNIE0gWCBcXHRpbWVzIE0gTSBYKSAiXSxbNywwLCJNIE0gKE0gTSBYIFxcdGltZXMgTSBYKSJdLFs5LDAsIk1NTU1YIl0sWzExLDAsIk0gTSBNIFgiXSxbMTIsMiwiTSBNIFgiXSxbMCwxLCJcXG11Il0sWzAsMiwiTSBcXGRlbHRhIiwyXSxbMiwzLCJcXGRlbHRhIiwyXSxbMyw0LCJNIFxcbGFuZ2xlIE0gXFxlcHNpbG9uLCBcXGVwc2lsb24gXFxyYW5nbGUiLDJdLFs0LDUsIk0gXFx0ZXh0cm17c3RyfSIsMl0sWzUsNiwiTSBNIFxcdGV4dHJte3B1dH0iLDJdLFs2LDcsIlxcbXUiLDJdLFs3LDgsIk0gXFxtdSIsMl0sWzEsOCwiXFxkZWx0YSJdXQ==*)



Definition axiom5alt := forall A,
  coMult * (@mult A) = (#mult) * mult * (#(# put)) * (# str) * (#<| #coUnit, coUnit|>) * coMult * (#coMult). 


(*Now, we show that this formulation is equivalent to the original one*)
(*For this we prove that the righthand side is equal to the right-hand side of multCoMult axiom*)
Theorem  flattenExpandAltThm : forall A, forall (x : M (M A)), 
  mult ( (#(# mult)) ( ((#(#put)) ((# str) ((#<| id, coMult * coUnit|>) (coMult x)))))) = 
  ((#mult) * mult * (#(# put)) * (# str) * (#<| #coUnit, coUnit|>) * coMult * (#coMult)) x.
Proof.
  intros. 
  unfold compose.
  rewrite multNatural.
  rewrite coMultNatural. 
  replace  (fun x0 : M (M A) => coMult (coUnit x0)) with ((@coMult A) * coUnit)
  by (apply functional_extensionality ; intros; reflexivity).
  repeat rewrite mapCompose.
  unfold compose.
  unfold pairing.
  replace (fun x0 : M (M A) => (# put) (str ((# coUnit) ((# coMult) x0), coUnit ((# coMult) x0)))) 
  with (fun x0 : M (M A) => (# put) (str (x0, coMult (coUnit x0)))) by
 (apply functional_extensionality; intros;  rewrite <- coUnitNatural;
  rewrite mapCompose;
  unfold compose;
  (replace (fun x1 : M A => coUnit (coMult x1)) with (@id (M A)) by
  (apply functional_extensionality; intros; rewrite coUnitCoMultAx; reflexivity));
  rewrite mapId;
  reflexivity).
  unfold id.
  reflexivity.
Qed.

End alternativeDefinition.

