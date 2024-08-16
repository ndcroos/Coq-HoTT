Require Import Basics.Overture Basics.Tactics WildCat.Core AbelianGroup
  AbGroups.Z Spaces.Int Groups.QuotientGroup Basics.Trunc Truncations.Core Spaces.Nat.Core.

(** * Cyclic groups *)

(** The [n]-th cyclic group is the cokernel of [ab_mul n]. *)
Definition cyclic (n : nat) : AbGroup
  := ab_cokernel (ab_mul (A:=abgroup_Z) n).

Definition cyclic_in (n : nat) : abgroup_Z $-> cyclic n
  := grp_quotient_map. 

Definition ab_mul_cyclic_in (n : nat) (x y : abgroup_Z)
  : ab_mul y (cyclic_in n x) = cyclic_in n (y * x)%int.
Proof.
  lhs_V nrapply ab_mul_natural.
  apply ap, abgroup_Z_ab_mul.
Defined.

(** Recursion principle for `cyclic`. *)

Definition cyclic_rec (n : nat) {G : Group} (g : G) (p : grp_pow g n = mon_unit)
  : GroupHomomorphism (cyclic n) G.
Proof.
  snrapply grp_quotient_rec.
  1: apply grp_pow_homo; assumption.
  1: simpl. 
  intros x y.
  strip_truncations.
  destruct y as [a H].
  change (ab_mul n a) in H.
Defined.

(*
Definition cyclic_rec_beta_in (n k : nat) {G : Group} (g : G)
  (p : grp_pow g n = mon_unit)
  : cyclic_rec n g p (cyclic_in n k) = grp_pow g k
  := idpath.s
*)


(** Induction principle for `cyclic`. *)
Definition cyclic_ind_hprop (n : nat) (P : cyclic n -> Type)
  `{forall x, IsHProp (P x)}
  (H1 : forall (x : nat), P (cyclic_in n x))
  (H2 : forall x, P x -> P (negate x))
  : forall x, P x.
Proof.
  srapply grp_quotient_ind_hprop.
  unfold cyclic_in in H1.
Defined.

(*
(** Induction principle for `cyclic` landing in a homotopy of group homomorphisms. *)
Definition cyclic_ind_homotopy (n : nat) {G : Group}
  (f g : GroupHomomorphism (cyclic n) G)
  (p : forall (k : nat), f (cyclic_in n k) = g (cyclic_in n k))
  : f == g.


Definition cyclic_ind_homotopy_op (n : nat) {A : AbGroup}
  (f f' f'' : (cyclic n) $-> A)
  (p : forall (k : nat), f (cyclic_in n k) = f' (cyclic_in n k) + f'' (cyclic_in n k))
  : forall x, f x = f' x + f'' x
  := cyclic_ind_homotopy n _ (ab_homo_add f' f'') p.
*)

Definition cyclic_in_mod (n : nat) (x : nat)
  : cyclic_in n x = cyclic_in n (x mod n)%nat.
Proof.
  snrapply grp_quotient_rec.
Defined.

Definition cyclic_in_divides n m : (n | m)%nat -> cyclic_in n m = mon_unit.
