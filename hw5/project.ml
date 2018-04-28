(* Name: LeAnn Gove *)
(*Collaboration statement: I worked with Madison Anderson on this homework and received help from Ramy Koudsi*)
(* Course: UVM CS 225 Spring 2018 - Darais *)
(* HW: HW5 *)

open Util
open StringSetMap

(* The Assignment:
 * 
 * Fill in the `raise TODO` parts of the code:
 * - 22 cases in the `step` function
 * - 07 cases in the `scope_ok` function
 * - 08 cases in the `infer` function
 *
 * See the writeup for the specification for `step`, `scope_ok` and `infer`
 * functions that you must implement.
 *
 * Passing all of the tests does not guarantee 100%. You may want to write some
 * tests of your own.
 *
 * The last case of `infer` is for unpack expressions. In both the writeup and
 * code we define an alternative (and equivalent) rule [Unpack-Alt] which is
 * more suggestive of an implementation than the original rule [Unpack].
 *
 * If you ever need to compare two types for equality, use the function tequal,
 * and not (=). tequal will compare types for alpha-equivalence, e.g., ∀X.X and
 * ∀Y.Y are alpha equivalent, so tequal (∀Y.Y) (∀X.X) will return true, whereas
 * (∀Y.Y) = (∀X.X) using OCaml's (=) operation will return false.
 *
 * You may find the following functions helpful:
 *
 * The empty string set: 
 *   
 *   on paper: {}
 *   in OCaml: StringSet.empty
 *
 * The singleton string set:
 *
 *   on paper: {x}
 *   in OCaml: StringSet.singleton x
 *   or      : StringSet.of_list [x]
 *
 * String set union:
 *
 *   on paper: S₁ ∪ S₂
 *   in OCaml: StringSet.union s1 s2
 *
 * Removing from a string set:
 *
 *   on paper: S \ {x}
 *   in OCaml: StringSet.remove x s
 *
 * Testing membership in a string set:
 *
 *   on paper: x ∈ S
 *   in OCaml: StringSet.mem x s
 *
 * Analogously for maps:
 *
 *   on paper: {}
 *   in OCaml: StringMap.empty
 *
 *   on paper: {x ↦ τ}
 *   in OCaml: StringMap.singleton x t
 *
 *   on paper: Γ[x ↦ τ]
 *   in OCaml: StringMap.add x t g
 *
 *   on paper Γ(x) = τ
 *   in OCaml: StringMap.find x g = t
 *
 * Remember to always use OCaml's structural equality (=), and never use
 * physical equality (==).
 *)

(********************
 * Syntax for types *
 ********************)

(* X ∈ tvar ≈ 𝕊
 *)
type tvar = string
[@@deriving show {with_path = false}]

(* τ ∈ type ⩴ bool | nat | top | τ × τ | τ → τ | X | ∀X.τ | ∃X.τ
 *)
type ty =
  | Bool
  | Nat
  | Top
  | Prod of ty * ty
  | Fun of ty * ty
  | TVar of tvar
  | Forall of tvar * ty
  | Exists of tvar * ty

[@@deriving show {with_path = false}]

(**************************
 * Syntax for expressions *
 **************************)

(* x ∈ var ≈ 𝕊
 *)
type var = string
[@@deriving show {with_path = false}]

(* e ∈ exp ⩴ true | false | if(e){e}{e}
 *         | zero | succ(e) | pred(e) | iszero(e)
 *         | ⟨e,e⟩ | projl(e) | projr(e)
 *         | x | let x ≔ e in e | λ(x:τ).e | e(e)
 *         | ΛX.e | e[τ]
 *         | ⟨*τ,e⟩ as ∃X.τ | let ⟨*X,x⟩ = e in e | λX <:T .t
 *)
type exp =
  | True
  | False
  | If of exp * exp * exp
  | Zero
  | Succ of exp
  | Pred of exp
  | IsZero of exp
  | Pair of exp * exp
  | Projl of exp
  | Projr of exp
  | Var of var
  | Let of var * exp * exp
  | Lambda of var * ty * exp
  | Apply of exp * exp
  | BigLambda of tvar * exp
  | TyApply of exp * ty
  | Pack of ty * exp * tvar * ty
  | Unpack of tvar * var * exp * exp
  | Abstraction of tvar * ty * exp
[@@deriving show {with_path = false}]

(*********************
 * Syntax for values *
 *********************)

(* nv ∈ nval ⩴ zero | succ(nv)
 *)
type natval =
  | VZero
  | VSucc of natval
[@@deriving show {with_path = false}]

(* v ∈ value ⩴ true | false
 *           | n
 *           | ⟨v,v⟩
 *           | λ(x:τ).e
 *           | ΛX.e
 *           | ⟨*τ,v⟩ as ∃X.τ
             | λX <:T.t
 *)
type value =
  | VTrue
  | VFalse
  | VNat of natval
  | VPair of value * value
  | VLambda of var * ty * exp
  | VBigLambda of tvar * exp
  | VPack of ty * value * tvar * ty
  | VAbstraction of tvar * ty * exp
[@@deriving show {with_path = false}]

(***********************************
 * Syntax for type system contexts *
 ***********************************)

(* Γ ∈ tenv ≔ var ⇀ type
 *)
type tscope = string_set
[@@deriving show {with_path = false}]

(* S ∈ scope ≔ ℘(tvar)
 *)
type tenv = ty string_map
[@@deriving show {with_path = false}]

(****************************
 * Free variables for types *
 ****************************)

(* FV ∈ type → ℘(tvar) 
 * tfree_vars τ ≡ FV(τ)
 *)
let rec tfree_vars (t0 : ty) : string_set = match t0 with
  | Bool -> StringSet.empty
  | Nat -> StringSet.empty
  | Prod(t1,t2) -> StringSet.union (tfree_vars t1) (tfree_vars t2)
  | Fun(t1,t2) -> StringSet.union (tfree_vars t1) (tfree_vars t2)
  | TVar(xt) -> StringSet.of_list [xt]
  | Forall(xt,t) -> StringSet.remove xt (tfree_vars t)
  | Exists(xt,t) -> StringSet.remove xt (tfree_vars t)
  | Top -> raise TODO

(**************************
 * Substitution for types *
 **************************)

(* An auxiliary function:
 * 
 *   trename X X′ τ
 *
 * for renaming X to X′ in type τ, i.e., [X↦X′]τ
 *)
let rec trename (xt : tvar) (xt' : tvar) (t0 : ty) : ty = match t0 with
  | Bool -> Bool
  | Nat -> Nat
  | Prod(t1,t2) -> Prod(trename xt xt' t1,trename xt xt' t2)
  | Fun(t1,t2) -> Fun(trename xt xt' t1,trename xt xt' t2)
  | TVar(yt) -> if xt = yt then TVar(xt') else TVar(yt)
  | Forall(yt,t) -> if xt = yt then Forall(yt,t) else Forall(yt,trename xt xt' t)
  | Exists(yt,t) -> if xt = yt then Exists(yt,t) else Forall(yt,trename xt xt' t)
  | Top -> raise TODO

(* An auxiliary function:
 *
 *   tfresh X τ′ τ = ⟨X′,τ″⟩
 *
 * which returns X′ and τ″ such that
 *
 *   X′ ∉ FV(τ′) ∪ (FV(τ) ∖ ❴X❵)
 *   τ″ = [X↦X′]τ
 *
 * we first define an iterator helper function:
 *
 *   tfresh_i X X′ τ′ τ
 *
 * which tries the current candidate X′, and iterates to try X′ with a prime
 * appended to the variable symbol if X′ isn't satisfactory.
 *
 * a call to
 *
 *   tfresh X τ′ τ 
 *
 * runs the iterator with X as the current guess.
 *)
let rec tfresh_i (xt : tvar) (xt' : tvar) (t' : ty) (t : ty) : tvar * ty =
  if StringSet.mem xt' (StringSet.union (tfree_vars t') (tfree_vars (Forall(xt,t))))
  then tfresh_i xt (xt' ^ "'") t' t
  else (xt',trename xt xt' t)

let tfresh (xt : tvar) (t' : ty) (t : ty) : tvar * ty = tfresh_i xt xt t' t

(* The capture-avoiding substitution function for types.
 *
 * [_↦_]_ ∈ tvar × type × type → type
 * tsubst X τ′ τ ≡ [X↦τ′]τ
 *)
let rec tsubst (xt : tvar) (t' : ty) (t0 : ty) = match t0 with
  | Bool -> Bool
  | Nat -> Nat
  | Prod(t1,t2) -> Prod(tsubst xt t' t1,tsubst xt t' t2)
  | Fun(t1,t2) -> Fun(tsubst xt t' t1,tsubst xt t' t2)
  | TVar(yt) -> if xt = yt then t' else TVar(yt)
  | Forall(yt,t) -> 
      if xt = yt then Forall(xt,t) else 
      let (yt'',t'') = tfresh yt t' t in
      Forall(yt'',tsubst xt t' t'')
  | Exists(yt,t) ->
      if xt = yt then Exists(xt,t) else 
      let (yt'',t'') = tfresh yt t' t in
      Exists(yt'',tsubst xt t' t'')
  | Top -> raise TODO

(**********************************
 * Free variables for expressions *
 **********************************)

(* FV ∈ exp → ℘(var)
 * efree_vars e ≡ FV(e)3
 *)
let rec efree_vars (e0 : exp) : string_set = match e0 with
  | True -> StringSet.empty
  | False -> StringSet.empty
  | If(e1,e2,e3) -> 
      StringSet.union 
        (efree_vars e1) 
        (StringSet.union (efree_vars e2) (efree_vars e3))
  | Zero -> StringSet.empty
  | Succ(e) -> efree_vars e
  | Pred(e) -> efree_vars e
  | IsZero(e) -> efree_vars e
  | Pair(e1,e2) -> StringSet.union (efree_vars e1) (efree_vars e2)
  | Projl(e) -> efree_vars e
  | Projr(e) -> efree_vars e
  | Var(x) -> StringSet.of_list [x]
  | Let(x,e1,e2) -> 
      StringSet.union 
        (efree_vars e1)
        (StringSet.remove x (efree_vars e2))
  | Lambda(x,t,e) ->
      StringSet.remove x (efree_vars e)
  | Apply(e1,e2) -> StringSet.union (efree_vars e1) (efree_vars e2)
  | BigLambda(xt,e) -> efree_vars e
  | TyApply(e,t) -> efree_vars e
  | Pack(t1,e,xt,t2) -> efree_vars e
  | Unpack(xt,x,e1,e2) -> 
      StringSet.union 
        (efree_vars e1)
        (StringSet.remove x (efree_vars e2))
  | Abstraction(xt,t,e) -> efree_vars e

(***********************************************
 * Substitution for expressions in expressions *
 ***********************************************)

(* Non-capture-avoiding substitution for expressions in expressions. Because
 * this is non-capture-avoiding, it assumes that the expression being
 * substituted is closed.
 *
 *   esubst_e_i x e′ e
 *
 * Assumption: e′ is closed 
 *
 * Do not use this function directly. Instead, use esubst_e_i which checks the
 * invariant.
 *)
let rec esubst_e_i (x : var) (e' : exp) (e0 : exp) : exp = match e0 with
  | True -> True
  | False -> False
  | If(e1,e2,e3) -> If(esubst_e_i x e' e1,esubst_e_i x e' e2,esubst_e_i x e' e3)
  | Zero -> Zero
  | Succ(e) -> Succ(esubst_e_i x e' e)
  | Pred(e) -> Pred(esubst_e_i x e' e)
  | IsZero(e) -> IsZero(esubst_e_i x e' e)
  | Pair(e1,e2) -> Pair(esubst_e_i x e' e1,esubst_e_i x e' e2)
  | Projl(e) -> Projl(esubst_e_i x e' e)
  | Projr(e) -> Projr(esubst_e_i x e' e)
  | Var(y) -> if x = y then e' else Var(y)
  | Let(y,e1,e2) -> 
      if x = y 
      then Let(x,esubst_e_i x e' e1,e2)
      else Let(y,esubst_e_i x e' e1,esubst_e_i x e' e2)
  | Lambda(y,t,e) ->
      if x = y
      then Lambda(x,t,e)
      else Lambda(y,t,esubst_e_i x e' e)
  | Apply(e1,e2) -> Apply(esubst_e_i x e' e1,esubst_e_i x e' e2)
  | BigLambda(xt,e) -> BigLambda(xt,esubst_e_i x e' e)
  | TyApply(e,t) -> TyApply(esubst_e_i x e' e,t)
  | Pack(t1,e,xt,t2) -> Pack(t1,esubst_e_i x e' e,xt,t2)
  | Unpack(xt,y,e1,e2) -> 
      if x = y
      then Unpack(xt,x,esubst_e_i x e' e1,e2)
      else Unpack(xt,y,esubst_e_i x e' e1,esubst_e_i x e' e2)
  | Abstraction(yt,t,e) -> Abstraction(yt,t,esubst_e_i x e' e)

exception NOT_CLOSED_ERROR

(* A version of non-capture-avoiding substitution that raises an exception if
 * its required assumptions are not satisfied.
 *
 * [_↦_]_ ∈ var × exp × exp → exp
 * esubst_e x e′ e ≡ [x↦e′]e
 *
 * Raises exception if e′ is not closed
 *)
let esubst_e (x : var) (e' : exp) (e : exp) : exp =
  if StringSet.equal (efree_vars e') StringSet.empty
  then esubst_e_i x e' e
  else raise NOT_CLOSED_ERROR

(*****************************************
 * Substitution for types in expressions *
 *****************************************)

(* Non-capture-avoiding substitution for types in expressions. Because this is
 * non-capture-avoiding, it assumes that the type being substituted is closed.
 *
 *   esubst_t_i X τ′ e
 *
 * Assumption: τ′ is closed 
 *
 * Do not use this function directly. Instead, use esubst_t_i which checks the
 * invariant.
 *)
let rec esubst_t_i (xt : tvar) (t' : ty) (e0 : exp) : exp = match e0 with
  | True -> True
  | False -> False
  | If(e1,e2,e3) -> If(esubst_t_i xt t' e1,esubst_t_i xt t' e2,esubst_t_i xt t' e3)
  | Zero -> Zero
  | Succ(e) -> Succ(esubst_t_i xt t' e)
  | Pred(e) -> Pred(esubst_t_i xt t' e)
  | IsZero(e) -> IsZero(esubst_t_i xt t' e)
  | Pair(e1,e2) -> Pair(esubst_t_i xt t' e1,esubst_t_i xt t' e2)
  | Projl(e) -> Projl(esubst_t_i xt t' e)
  | Projr(e) -> Projr(esubst_t_i xt t' e)
  | Var(x) -> Var(x)
  | Let(x,e1,e2) -> Let(x,esubst_t_i xt t' e1,esubst_t_i xt t' e2)
  | Lambda(x,t,e) -> Lambda(x,tsubst xt t' t,esubst_t_i xt t' e)
  | Apply(e1,e2) -> Apply(esubst_t_i xt t' e1,esubst_t_i xt t' e2)
  | BigLambda(yt,e) -> 
      if xt = yt
      then BigLambda(xt,e)
      else BigLambda(yt,esubst_t_i xt t' e)
  | TyApply(e,t) -> TyApply(esubst_t_i xt t' e,tsubst xt t' t)
  | Pack(t1,e,yt,t2) -> 
      if xt = yt
      then Pack(tsubst xt t' t1,esubst_t_i xt t' e,xt,t2)
      else Pack(tsubst xt t' t1,esubst_t_i xt t' e,yt,tsubst xt t' t2)
  | Unpack(yt,x,e1,e2) -> 
      if xt = yt
      then Unpack(xt,x,esubst_t_i xt t' e1,e2)
      else Unpack(xt,x,esubst_t_i xt t' e1,esubst_t_i xt t' e2)
  | Abstraction(yt,t,e) ->
      if xt = yt
      then Abstraction(xt,t,esubst_t_i xt t' e)
      else Abstraction(xt,tsubst xt t' t,esubst_t_i xt t' e)

(* A version of non-capture-avoiding substitution that raises an exception if
 * its required assumptions are not satisfied.
 *
 * [_↦_]_ ∈ tvar × type × exp → exp
 * esubst_t X τ′ e ≡ [X↦τ′]e
 *
 * Raises exception if τ′ is not closed
 *)
let esubst_t (x : var) (t' : ty) (e : exp) : exp =
  if StringSet.equal (tfree_vars t') StringSet.empty
  then esubst_t_i x t' e
  else raise NOT_CLOSED_ERROR

(**********************************
 * Small step transition relation *
 **********************************)

(* Converting natval to exp *)
let rec exp_of_natval (nv0 : natval) : exp = match nv0 with
  | VZero -> Zero
  | VSucc(nv) -> Succ(exp_of_natval nv)

(* Converting val to exp *)
let rec exp_of_val (v0 : value) : exp = match v0 with
  | VTrue -> True
  | VFalse -> False
  | VNat(nv) -> exp_of_natval nv
  | VPair(v1,v2) -> Pair(exp_of_val v1,exp_of_val v2)
  | VLambda(x,t,e) -> Lambda(x,t,e)
  | VBigLambda(xt,e) -> BigLambda(xt,e)
  | VPack(t1,v,xt,t2) -> Pack(t1,exp_of_val v,xt,t2)
  | VAbstraction(xt, ty, e) -> Abstraction(xt, ty, e)

(* A result is either a value, an expression, or the symbol `stuck`.
 *
 * r ∈ result ⩴ v | e | stuck
 *)
type result =
  | Val of value
  | Step of exp
  | Stuck
[@@deriving show {with_path = false}]


(* The small-step relation e —→ e
 *
 * Assumption: e is closed.
 *
 * If step(e) = v, then e is a value (and does not take a step).
 * (i.e., e ∈ val)
 *
 * If step(e) = e′, then e steps to e′.
 * (i.e., e —→ e′)
 *
 * If step(e) = stuck, then e is stuck, that is e is not a value and does not
 * take a step.
 * (i.e., e ∉ val and e —↛)
 *)
let rec step (e0 : exp) : result = match e0 with
  (* true ∈ val *)
  | True -> Val(VTrue)
  (* false ∈ val *)
  | False -> Val(VFalse)
  | If(e1,e2,e3) -> begin match step e1 with
      (* [If-True] 
       * if(true){e₂}{e₃} —→ e₂ *)
      | Val(VTrue) -> Step(e2)
      (* [If-False] 
       * if(false){e₂}{e₃} —→ e₃ *)
      | Val(VFalse) -> Step(e3)
      (* v ∉ {true,false} 
       * ⟹  
       * if(v){e₂}{e₃} ∉ val
       * if(v){e₂}{e₃} —↛ *)
      | Val(_) -> Stuck
      (* [If-Cong] 
       * e₁ —→ e₁′ 
       * ⟹  
       * if(e₁){e₂}{e₃} —→ if(e₁′){e₂}{e₃} *)
      | Step(e1') -> Step(If(e1',e2,e3))
      (* e₁ ∉ val
       * e₁ —↛
       * ⟹ 
       * if(e₁){e₂}{e₃} ∉ val
       * if(e₁){e₂}{e₃} —↛ *)
      | Stuck -> Stuck
      end
  (* zero ∈ val *)
  | Zero -> Val(VNat(VZero))
  | Succ(e) -> begin match step e with
      (* nv ∈ nval
       * ⟹
       * succ(nv) ∈ nval ⊆ val *)
      | Val(VNat(nv)) -> Val(VNat(VSucc(nv)))
      (* v ∉ nval
       * ⟹
       * succ(v) ∉ val
       * succ(v) —↛ *)
      | Val(_) -> Stuck
      (* [Succ-Cong]
       * e —→ e′
       * succ(e) —→ succ(e′) *)
      | Step(e') -> Step(Succ(e'))
      (* e ∉ val
       * e —↛
       * ⟹
       * succ(e) ∉ val
       * succ(e) —↛ *)
      | Stuck -> Stuck
      end
  | Pred(e) -> begin match step e with
      (* [Pred-Zero]
       * pred(zero) —→ zero *)
      | Val(VNat(VZero)) -> Step(Zero)
      (* [Pred-Succ]
       * pred(succ(nv)) —→ nv *)
      | Val(VNat(VSucc(nv))) -> Step(exp_of_natval nv)
      (* v ∉ nval
       * ⟹
       * pred(v) ∉ val
       * pred(v) —↛ *)
      | Val(_) -> Stuck
      (* [Pred-Cong]
       * e —→ e′
       * ⟹
       * pred(e) —→ pred(e′) *)
      | Step(e') -> Step(Pred(e'))
      (* e ∉ val
       * e —↛
       * ⟹
       * pred(e) ∉ val
       * pred(e) —↛ *)
      | Stuck -> Stuck
      end
  | IsZero(e) -> begin match step e with
      (* [IsZero-Zero]
       * iszero(zero) —→ true *)
      | Val(VNat(VZero)) -> Step(True)
      (* [IsZero-Succ]
       * iszero(succ(nv)) —→ false *)
      | Val(VNat(VSucc(nv))) -> Step(False)
      (* v ∉ nval
       * ⟹
       * iszero(v) ∉ val
       * iszero(v) —↛ *)
      | Val(_) -> Stuck
      (* [IsZero-Cong]
       * e —→ e′
       * ⟹
       * iszero(e) —→ iszero(e′) *)
      | Step(e') -> Step(IsZero(e'))
      (* e ∉ val
       * e —↛
       * ⟹
       * iszero(e) ∉ val
       * iszero(e) —↛ *)
      | Stuck -> Stuck
      end
  | Pair(e1,e2) -> begin match step e1 with
      | Val(v1) -> begin match step e2 with
          (* ⟨v₁,v₂⟩ ∈ val *)
          | Val(v2) -> Val(VPair(v1,v2))
          (* [Pair-Cong-2]
           * e —→ e′
           * ⟹
           * ⟨v,e⟩ —→ ⟨v,e′⟩ *)
          | Step(e2') -> Step(Pair(e1,e2'))
          (* e ∉ val
           * e —↛
           * ⟹
           * ⟨v,e⟩ ∉ val
           * ⟨v,e⟩ —↛ *)
          | Stuck -> Stuck
          end
      (* [Pair-Cong-1]
       * e₁ —→ e₁′
       * ⟹
       * ⟨e₁,e₂⟩ —→ ⟨e₁′,e₂⟩ *)
      | Step(e1') -> Step(Pair(e1',e2))
      (* e₁ ∉ val
       * e₁ —↛
       * ⟹
       * ⟨e₁,e₂⟩ ∉ val
       * ⟨e₁,e₂⟩ —↛ *)
      | Stuck -> Stuck
      end
  | Projl(e1) -> begin match step e1 with
      (* [Projl-Pair]
       * projl(⟨v₁,v₂⟩) —→ v₁ *)
      | Val(VPair(v1,v2)) -> Step(exp_of_val v1)
      (* ∄v₁,v₂. v = ⟨v₁,v₂⟩
       * ⟹
       * projl(v) ∉ val
       * projl(v) —↛ *)
      | Val(_) -> Stuck
      (* [Projl-Cong]
       * e —→ e′
       * ⟹
       * projl(e) —→ projl(e′) *)
      | Step(e1') -> Step(Projl(e1'))
      (* e ∉ val
       * e —↛
       * ⟹
       * projl(e) ∉ val
       * projl(e) —↛ *)
      | Stuck -> Stuck
      end
  | Projr(e1) -> begin match step e1 with
      (* [Projr-Pair]
       * projr(⟨v₁,v₂⟩) —→ v₂ *)
      | Val(VPair(v1,v2)) -> Step(exp_of_val v2)
      (* ∄v₁,v₂. v = ⟨v₁,v₂⟩
       * ⟹
       * projr(v) ∉ val
       * projr(v) —↛ *)
      | Val(_) -> Stuck
      (* [Projr-Cong]
       * e —→ e′
       * ⟹
       * projr(e) —→ projr(e′) *)
      | Step(e1') -> Step(Projr(e1'))
      (* e ∉ val
       * e —↛
       * ⟹
       * projr(e) ∉ val
       * projr(e) —↛ *)
      | Stuck -> Stuck
      end
  (* x is not closed *)
  | Var(x) -> raise NOT_CLOSED_ERROR
  | Let(x,e1,e2) -> begin match step e1 with
      (* [Let-Val]
       * let x ≔ v in e —→ [x↦v]e *)
      | Val(v1) -> let e11 = exp_of_val v1 in
       Step(esubst_e x e11 e2)

      (* [Let-Cong]
       * e₁ —→ e₁′
       * ⟹
       * let x ≔ e₁ in e₂ —→ let x = e₁′ in e₂ *)
      | Step(e1') -> Step(Let(x,e1',e2))
      (* e₁ ∉ val
       * e₁ —↛
       * ⟹
       * let x ≔ e₁ in e₂ ∉ val
       * let x ≔ e₁ in e₂ —↛ *)
      | Stuck -> Stuck
      end
  (* λ(x:τ).e ∈ val *)
  | Lambda(x,t,e) -> Val(VLambda(x,t,e))
  | Apply(e1,e2) -> begin match step e1 with
      | Val(v1) -> begin match step e2 with
          | Val(v2) -> begin match v1 with
              (* [Apply-Lambda (β)]
               * (λ(x:τ).e)v —→ [x↦v]e *)
              | VLambda(x,t,e) -> Step(esubst_e x e2 e)
              (* ∄x,τ,e. v₁ = λ(x:τ).e
               * ⟹
               * v₁(v₂) ∉ val
               * v₁(v₂) —↛ *)
              | _ -> Stuck
              end
          (* [Apply-Cong-2]
           * e —→ e′
           * ⟹
           * v(e) —→ v(e′) *)
          | Step(e2') -> Step(Apply(e1,e2'))
          (* e ∉ val
           * e —↛
           * ⟹
           * v(e) ∉ val
           * v(e) —↛ *)
          | Stuck -> Stuck
          end
      (* [Apply-Cong-1]
       * e₁ —→ e₁′
       * ⟹
       * e₁(e₂) —→ e₁′(e₂) *)
      | Step(e1') -> Step(Apply(e1',e2))
      (* e₁ ∉ val
       * e₁ —↛
       * ⟹
       * e₁(e₂) ∉ val
       * e₁(e₂) –↛ *)
      | Stuck -> Stuck
      end
  (* ΛX.e ∈ val *)
  | BigLambda(xt,e) -> Val(VBigLambda(xt,e))
  | TyApply(e,t) -> begin match step e with
      (* [Type-Apply-Lambda]
       * (ΛX.e)[τ] —→ [X↦τ]e *)
      | Val(VBigLambda(xt,e')) -> Step(esubst_t xt t e')
      (* ∄X,e. v = ΛX.e
       * ⟹
       * v[τ] ∉ val
       * v[τ] —↛ *)
      | Val(VAbstraction(xt,t,e')) -> Step(esubst_t xt t e')
      (* | Val(VAbstraction(xt, t11, t12)) -> Step(tsubst xt (TVar(t)) t12) *)
      (* ∄X,e. v = ΛX.e
       * ⟹
       * v[τ] ∉ val
       * v[τ] —↛ *)
      | Val(_) -> Stuck
      (* [Type-Apply-Cong]
       * e —→ e′
       * ⟹
       * e[τ] —→ e′[τ] *)
      | Step(e') -> Step(TyApply(e',t))
      (* e ∉ val
       * e —↛
       * ⟹
       * e[τ] ∉ val
       * e[τ] —↛ val *)
      | Stuck -> Stuck
      end
  | Pack(t1,e,xt,t2) -> begin match step e with
      (* ⟨*τ,v⟩ as ∃X.τ ∈ val *)
      | Val(v) -> Val(VPack(t1,v,xt,t2))
      (* [Pack-Cong]
       * e —→ e′
       * ⟹
       * ⟨*τ,e⟩ as ∃X.τ —→ ⟨*τ,e′⟩ as ∃X.τ *)
      | Step(e') -> Step(Pack(t1,e',xt,t2))
      (* e ∉ val
       * e —↛
       * ⟹
       * ⟨*τ,e⟩ as ∃X.τ ∉ val
       * ⟨*τ,e⟩ as ∃X.τ —↛ *)
      | Stuck -> Stuck
      end
  | Unpack(xt,x,e1,e2) -> begin match step e1 with
      (* [Unpack-Pack]
       * let ⟨*X,x⟩ ≔ ⟨*τ′,v⟩ as ∃X.τ in e —→ [X↦τ′][x↦v]e *)
      | Val(VPack(t1,v,yt,t2)) -> 
      let first = esubst_e x (exp_of_val v) e2 in
      let second = esubst_t xt t1 first in
      Step(second)
      (* ∄ τ′,v′,X,τ. v = ⟨*τ′,v′⟩ as ∃X.τ
       * ⟹
       * let ⟨*X,x⟩ ≔ v in e ∉ val
       * let ⟨*X,x⟩ ≔ v in e —↛ *)
      | Val(_) -> Stuck
      (* [Unpack-Cong]
       * e₁ —→ e₁′
       * let ⟨*X,x⟩ ≔ e₁ in e₂ —→ let ⟨*X,x⟩ ≔ e₁′ in e₂ *)
      | Step(e1') -> Step(Unpack(xt,x,e1',e2))
      (* e₁ ∉ val
       * e₁ —↛
       * ⟹
       * let ⟨*X,x⟩ ≔ e₁ in e₂ ∉ val
       * let ⟨*X,x⟩ ≔ e₁ in e₂ —↛ *)
      | Stuck -> Stuck
      end
 | Abstraction(xt,ty,e) -> Val(VAbstraction(xt,ty,e))

(* The reflexive transitive closure of the small-step relation e —→* e *)
let rec step_star (e : exp) : exp = match step e with
  | Val(v) -> exp_of_val v
  | Step(e') -> step_star e'
  | Stuck -> e

(**********************
 * Well-scoped relation
 **********************)

(* The relation:
 *
 *   S ⊢ τ
 *
 * scope_ok S τ = true ⟺  S ⊢ τ
 *)
(* let rec scope_ok (s : tscope) (t0 : ty) : bool = match t0 with
  (* [Bool]
   * S ⊢ bool *)
  | Bool -> true
  (* [Nat]
   * S ⊢ nat *)
  | Nat -> true
  (* [Prod]
   * S ⊢ τ₁
   * S ⊢ τ₂
   * ⟹
   * S ⊢ τ₁ × τ₂ *)
  | Prod(t1,t2) -> let x = scope_ok s t1 in
  let y = scope_ok s t2 in
  y && x
  (* [Fun]
   * S ⊢ τ₁
   * S ⊢ τ₂
   * ⟹
   * S ⊢ τ₁ → τ₂ *)
  | Fun(t1,t2) -> let x = scope_ok s t1 in
  let y = scope_ok s t2 in
  y && x
  (* [TVar]
   * X ∈ S
   * ⟹
   * S ⊢ X *)
  | TVar(xt) -> StringSet.mem xt s
  (* [Forall]
   * S∪{X} ⊢ τ
   * ⟹
   * S ⊢ ∀X.τ *)
  | Forall(xt,t) -> let x = StringSet.singleton xt in
  let y = StringSet.union s x in
  scope_ok y t


  (* [Exists]
   * S∪{X} ⊢ τ
   * ⟹
   * S ⊢ ∃X.τ *)
  | Exists(xt,t) -> let x = StringSet.singleton xt in
  let y = StringSet.union s x in
  scope_ok y t *)


(***********************
 * Well-typed relation *
 ***********************)

(* An auxiliary function for testing the equality of two types, modulo alpha
 * conversion.
 *
 * First, a helper function tequal_r which keeps track of which bindings are
 * equal by assigning them to unique numbers.
 *)
let rec tequal_r (l : int) (t1e : int string_map) (t2e : int string_map) (t1 : ty) (t2 : ty) : bool = match t1 , t2 with
  | Bool , Bool -> true
  | Nat , Nat -> true
  | Fun(t11,t12) , Fun(t21,t22) -> tequal_r l t1e t2e t11 t21 && tequal_r l t1e t2e t12 t22
  | Prod(t11,t12) , Prod(t21,t22) -> tequal_r l t1e t2e t11 t21 && tequal_r l t1e t2e t12 t22
  | TVar(x) , TVar(y) -> 
      if StringMap.mem x t1e && StringMap.mem y t2e
      then StringMap.find x t1e = StringMap.find y t2e
      else x = y
  | Forall(xt,t1) , Forall(yt,t2) -> tequal_r (l+1) (StringMap.add xt l t1e) (StringMap.add yt l t2e) t1 t2
  | Forall(_) , _ -> false | _ , Forall(_) -> false
  | Exists(xt,t1) , Exists(yt,t2) -> tequal_r (l+1) (StringMap.add xt l t1e) (StringMap.add yt l t2e) t1 t2
  | _ , _ -> false

(* tequal τ₁ τ₂ = true ⟺  τ₁ ≈ᵅ τ₂ 
 *
 * !! use tequal in your implementation of infer anytime you need to compare
 * two types for equality 
 *)
let tequal (t1 : ty) (t2 : ty) : bool = tequal_r 1 StringMap.empty StringMap.empty t1 t2

exception TYPE_ERROR

(* The relation:
 *
 *   S , Γ ⊢ e : τ
 *
 * infer S Γ e = τ ⟺  S , Γ ⊢ : τ
 *)
(* let rec infer (s : tscope) (g : tenv) (e0 : exp) : ty = match e0 with
  (* [True]
   * S , Γ ⊢ true : bool *)
  | True -> Bool
  (* [False]
   * S , Γ ⊢ false : bool *)
  | False -> Bool
  (* [If]
   * S , Γ ⊢ e₁ : bool
   * S , Γ ⊢ e₂ : τ
   * S , Γ ⊢ e₃ : τ
   * ⟹
   * S , Γ ⊢ if(e₁){e₂}{e₃} : τ *)
  | If(e1,e2,e3) ->
      let t1 = infer s g e1 in
      let t2 = infer s g e2 in
      let t3 = infer s g e3 in
      if not (t1 = Bool) then raise TYPE_ERROR else
      if not (t2 = t3) then raise TYPE_ERROR else
      t2
  (* [Zero]
   * S , Γ ⊢ zero : nat *)
  | Zero -> Nat
  (* [Succ]
   * S , Γ ⊢ e : nat
   * ⟹
   * S , Γ ⊢ succ(e) : nat *)
  | Succ(e) ->
      let t = infer s g e in
      if not (t = Nat) then raise TYPE_ERROR else
      Nat
  (* [Pred]
   * S , Γ ⊢ e : nat
   * ⟹
   * S , Γ ⊢ pred(e) : nat *)
  | Pred(e) ->
      let t = infer s g e in
      if not (t = Nat) then raise TYPE_ERROR else
      Nat
  (* [IsZero]
   * S , Γ ⊢ e : nat
   * ⟹
   * S , Γ ⊢ iszero(e) : bool *)
  | IsZero(e) ->
      let t = infer s g e in
      if not (t = Nat) then raise TYPE_ERROR else
      Bool
  (* [Pair]
   * S , Γ ⊢ e₁ : τ₁
   * S , Γ ⊢ e₂ : τ₂
   * ⟹
   * S , Γ ⊢ ⟨e₁,e₂⟩ : τ₁ × τ₂ *)
  | Pair(e1,e2) ->
      let t1 = infer s g e1 in
      let t2 = infer s g e2 in
      Prod(t1,t2)
  (* [Projl]
   * S , Γ ⊢ e : τ₁ × τ₂
   * ⟹
   * S , Γ ⊢ projl(e) : τ₁ *)
  | Projl(e) ->
      let t = infer s g e in
      begin match t with
      | Prod(t1,_) -> t1
      | _ -> raise TYPE_ERROR
      end
  (* [Projr]
   * S , Γ ⊢ e : τ₁ × τ₂
   * ⟹
   * S , Γ ⊢ projr(e) : τ₂ *)
  | Projr(e) ->
      let t = infer s g e in
      begin match t with
      | Prod(_,t2) -> t2
      | _ -> raise TYPE_ERROR
      end
  (* [Var]
   * Γ(x) = τ
   * ⟹
   * S , Γ ⊢ x : τ *)
  | Var(x) -> StringMap.find x g
  (* [Var]
   * S , Γ ⊢ e₁ : τ₁
   * S , Γ[x↦τ₁] ⊢ e₂ : τ₂
   * ⟹
   * S , Γ ⊢ let x ≔ e₁ in e₂ : τ₂ *)
  | Let(x,e1,e2) -> let t1 = infer s g e1 in
  let z = StringMap.add x t1 g in 
  let t2 = infer s z e2 in
  t2

  (* [Lambda]S
   * S ⊢ τ₁
   * S , Γ[x↦τ₁] ⊢ e : τ₂
   * ⟹
   * S , Γ ⊢ λ(x:τ₁).e : τ₁ → τ₂ *)
  | Lambda(x,t1,e) -> if (scope_ok s t1) then
  let t12 = StringMap.add x t1 g in
  let t2 = infer s t12 e in
  Fun(t1,t2)
  else raise TYPE_ERROR

  (* [Apply]
   * S , Γ ⊢ e₁ : τ₁ → τ₂
   * S , Γ ⊢ e₂ : τ₁
   * ⟹
   * S , Γ ⊢ e₁(e₂) : τ₂ *)
  | Apply(e1,e2) -> let t = infer s g e1 in
  let t1 = infer s g e2 in 
  begin match t with 
    |Fun(t11,t2) -> if (tequal t11 t1) then t2 else raise TYPE_ERROR
    | _ -> raise TYPE_ERROR
  end
  (* [TypeLambda]
   * S∪{X} , Γ ⊢ e : τ
   * ⟹
   * S , Γ ⊢ ΛX.e : ∀X.τ *)
  | BigLambda(xt,e) ->
  let y = StringSet.of_list [xt] in
  let z = StringSet.union s y in
  let t1 = infer z g e in
 Forall(xt,t1)

  (* [TypeApply]
   * S ⊢ τ′
   * S , Γ ⊢ e : ∀X.τ
   * ⟹
   * S , Γ ⊢ e[τ′] : [X↦τ′]τ *)
  | TyApply(e,t') -> 
  if (scope_ok s t') then
  let t1 = infer s g e in
  begin match t1 with
    |Forall(xt,t) -> tsubst xt t' t
    | _ -> raise TYPE_ERROR
  end
else raise TYPE_ERROR

  (* [Pack]
   * S , Γ ⊢ e : [X↦τ′]τ
   * ⟹
   * S , Γ ⊢ ⟨*τ′,e⟩ as ∃ X.τ : ∃X.τ *)
  | Pack(t1,e,xt,t2) -> 
  let t11 = infer s g e in
  let boom = tsubst xt t1 t2 in
  if (tequal t11 boom) then
  Exists(xt,t2)
else raise TYPE_ERROR

  (* [Unpack-Alt]
   * S ⊢ τ₂
   * S , Γ ⊢ e₁ : ∃Y.τ₁
   * S∪{X} , Γ[x↦[Y↦X]τ₁] ⊢ e₂ : τ₂
   * ⟹
   * let ⟨*X,x⟩ ≔ e₁ in e₂ : τ₂ *)
  | Unpack(xt,x,e1,e2) -> 
    let type_of_e1 = infer s g e1 in
    begin match type_of_e1 with
      |Exists(y,t1) -> 
      (*THIRD RULE*)
      let beep = StringSet.of_list [xt] in
      let z = StringSet.union s beep in

      let sub = tsubst y (TVar(xt)) t1 in
      let finalsub = StringMap.add x sub g in 

      let t2 = infer z finalsub e2 in
      if (scope_ok s t2) then t2 
     else raise TYPE_ERROR
      | _ -> raise TYPE_ERROR
    end *)

(***********
 * Testing *
 ***********)

type 'a test_result =
  | R of 'a
  | TypeError
  | NotClosedError
[@@deriving show {with_path = false}]

let step_test_result (e : exp) : result test_result =
  try
    R(step e)
  with
    | TYPE_ERROR -> TypeError
    | NOT_CLOSED_ERROR -> NotClosedError

(* let infer_test_result (e : exp) : ty test_result =
  try
    R(infer StringSet.empty StringMap.empty e)
  with
    | TYPE_ERROR -> TypeError
    | NOT_CLOSED_ERROR -> NotClosedError *)

let step_tests : test_block =
  let pid : exp = Abstraction("X",Bool,Lambda("x",TVar("X"),Var("x"))) in
  (* let pid : exp = BigLambda("X",Lambda("x",TVar("X"),Var("x"))) in *)
  let pidid : exp = Lambda("x",Forall("X",Fun(TVar("X"),TVar("X"))),Var("x")) in
  let ppid : exp = BigLambda("X",pid) in
  let fiveo : exp = Pack(Nat,Pair(Zero,Lambda("x",Nat,Var("x"))),"X",Prod(TVar("X"),Fun(TVar("X"),TVar("X")))) in
  let unp : exp = Unpack("Y","y",fiveo,Pack(TVar("Y"),Apply(Projr(Var("y")),Projl(Var("y"))),"Z",TVar("Z"))) in
  TestBlock
  ( "STEP"
  , [ pid                           , R(Val(VBigLambda("X",Lambda("x",TVar("X"),Var("x")))))
    ; TyApply(pid,Nat)              , R(Step(Lambda("x",Nat,Var("x"))))
    ; TyApply(pid,Bool)             , R(Step(Lambda("x",Bool,Var("x"))))
    ; TyApply(pid,TVar("Y"))        , NotClosedError
    ; TyApply(Apply(pidid,pid),Nat) , R(Step(TyApply(pid,Nat)))
    ; TyApply(ppid,Nat)             , R(Step(pid))
    ; fiveo                         , R(Val(VPack(Nat,VPair(VNat(VZero),VLambda("x",Nat,Var("x"))),"X",Prod(TVar("X"),Fun(TVar("X"),TVar("X"))))))
    ; unp                           , R(Step(Pack(Nat,Apply(Projr(Pair(Zero,Lambda("x",Nat,Var("x")))),Projl(Pair(Zero,Lambda("x",Nat,Var("x"))))),"Z",TVar("Z"))))
    ]
  , step_test_result
  , (=)
  , [%show : exp]
  , [%show : result test_result]
  )

(* let infer_tests = 
  (* pid = ΛX.λ(x:X).x 
   * pid : ∀X.X→X
   *)
  let pid : exp = BigLambda("X",Lambda("x",TVar("X"),Var("x"))) in
  let pidt : ty = Forall("X",Fun(TVar("X"),TVar("X"))) in
  (* pidid = λ(x:∀X.X→X).x
   * pidid = (∀X.X→X) → (∀X.X→X)
   *)
  let pidid : exp = Lambda("x",pidt,Var("x")) in
  let pididt : ty = Fun(pidt,pidt) in
  (* ppid = ΛX.ΛX.λ(x:X).x
   * ppid = ∀X.∀X.X→X
   *)
  let ppid : exp = BigLambda("X",pid) in
  let ppidt : ty = Forall("X",pidt) in
  (* fiveo = ⟨*nat,⟨0,(λ(x:nat).x)⟩⟩ as ∃X.X×(X→X) 
   * fiveo : ∃X.X×(X→X)
   *)
  let fiveo : exp = Pack(Nat,Pair(Zero,Lambda("x",Nat,Var("x"))),"X",Prod(TVar("X"),Fun(TVar("X"),TVar("X")))) in
  let fiveot = Exists("X",Prod(TVar("X"),Fun(TVar("X"),TVar("X")))) in
  (* fiveo′ = ⟨*nat,⟨0,(λ(x:nat).x)⟩⟩ as ∃X.X×(X→nat) 
   * fiveo′ : ∃X.X×(X→X)
   *)
  let fiveo' : exp = Pack(Nat,Pair(Zero,Lambda("x",Nat,Var("x"))),"X",Prod(TVar("X"),Fun(TVar("X"),Nat))) in
  let fiveo't = Exists("X",Prod(TVar("X"),Fun(TVar("X"),Nat))) in
  (* fiveobad = ⟨*nat,⟨0,(λ(x:nat).x)⟩⟩ as ∃X.X×(X→bool) 
   *)
  let fiveobad : exp = Pack(Nat,Pair(Zero,Lambda("x",Nat,Var("x"))),"X",Prod(TVar("X"),Fun(TVar("X"),Bool))) in
  (* unp = let ⟨*Y,y⟩ ≔ ⟨*nat,⟨0,(λ(x:nat).x)⟩⟩ as ∃X.X×(X→X) in ⟨*Y,projr(y)(projl(y))⟩ as ∃Z.Z
   * unp : ∃Z.Z
   *)
  let unp : exp = Unpack("Y","y",fiveo,Pack(TVar("Y"),Apply(Projr(Var("y")),Projl(Var("y"))),"Z",TVar("Z"))) in
  let unpt : ty = Exists("Z",TVar("Z")) in
  (* unp' = let ⟨*Y,y⟩ ≔ ⟨*nat,⟨0,(λ(x:nat).x)⟩⟩ as ∃X.X×(X→X) in ⟨*Y,pid[Y](projr(y)(projl(y)))⟩ as ∃Z.Z
   * unp' : ∃Z.Z
   *)
  let unp' : exp = Unpack("Y","y",fiveo,Pack(TVar("Y"),Apply(TyApply(pid,TVar("Y")),Apply(Projr(Var("y")),Projl(Var("y")))),"Z",TVar("Z"))) in
  let unp't : ty = Exists("Z",TVar("Z")) in
  (* bunp = let ⟨*Y,y⟩ ≔ ⟨*nat,⟨0,(λ(x:nat).x)⟩⟩ as ∃X.X×(X→X) in projr(y)(projl(y)) *)
  let bunp : exp = Unpack("Y","y",fiveo,Apply(Projr(Var("y")),Projl(Var("y")))) in
  (* pidpair = ΛX.ΛY.⟨(λ(x:X).x),(λ(x:Y).x)⟩
   * pidpair : ∀X.∀Y.(X→X)×(Y→Y)
   *)
  let _pidpair : exp = BigLambda("X",BigLambda("Y",Pair(TyApply(pid,TVar("X")),TyApply(pid,TVar("Y"))))) in
  let _pidpairt : ty = Forall("X",Forall("Y",Prod(Fun(TVar("X"),TVar("X")),Fun(TVar("Y"),TVar("Y"))))) in
  (* weird1 = (ΛY.pidpair)[nat]
   * weird1 : [Y↦nat](∀X.∀Y.(X→X)×(Y→Y)
   * weird1 : pidpairt
   *)
  let _weird1 : exp = TyApply(BigLambda("Y",_pidpair),Nat) in
  weird2 = ∀Y.pidpair[Y]
   * weird2 : ∀Y.[X↦Y](∀Y.(X→X)×(Y→Y))
   * weird2 : ∀Y.∀Y′.(Y→Y)×(Y′→Y′)
  
  let _weird2 : exp = BigLambda("Y",TyApply(_pidpair,TVar("Y"))) in
  let _weird2t : ty = Forall("Y",Forall("Y'",Prod(Fun(TVar("Y"),TVar("Y")),Fun(TVar("Y'"),TVar("Y'"))))) in
  (* weird3 = ΛY′.ΛY.(ΛX.ΛY.⟨⟨(λ(x:Y′).x),(λ(x:X).x)⟩,(λ(x:Y).x)⟩)[Y]
   * weird3 : ∀Y′.∀Y.[X↦Y](∀Y.(Y′→Y′)×(X→X)×(Y→Y))
   * weird3 : ∀Y′.∀Y.∀Y″.(Y′→Y′)×(Y→Y)×(Y″→Y″)
   *)
  let _weird3 : exp = BigLambda("Y'",BigLambda("Y"
                    ,TyApply
                    (BigLambda("X",BigLambda("Y"
                      ,Pair(Pair(TyApply(pid,TVar("Y'")),TyApply(pid,TVar("X"))),TyApply(pid,TVar("Y")))))
                    ,TVar("Y")))) in
  let _weird3t : ty = Forall("Y'",Forall("Y",Forall("Y''"
                       ,Prod(Prod(Fun(TVar("Y'"),TVar("Y'")),Fun(TVar("Y"),TVar("Y"))),Fun(TVar("Y''"),TVar("Y''")))))) in
  TestBlock
  ( "INFER"
  , [ Let("x",Zero,Var("x"))                , R(Nat)
    ; Lambda("x",Nat,Var("x"))              , R(Fun(Nat,Nat))
    ; Lambda("x",TVar("X"),Var("x"))        , TypeError
    ; Apply(Lambda("x",Nat,Var("x")),Zero)  , R(Nat)
    ; Apply(Lambda("x",Nat,Var("x")),True)  , TypeError
    ; pid                                   , R(pidt)
    ; TyApply(pid,Nat)                      , R(Fun(Nat,Nat))
    ; TyApply(pid,Bool)                     , R(Fun(Bool,Bool))
    ; TyApply(pid,TVar("Y"))                , TypeError
    ; pidid                                 , R(pididt)
    ; TyApply(Apply(pidid,pid),Nat)         , R(Fun(Nat,Nat))
    ; ppid                                  , R(ppidt)
    ; TyApply(ppid,Nat)                     , R(pidt)
    ; fiveo                                 , R(fiveot)
    ; fiveo'                                , R(fiveo't)
    ; fiveobad                              , TypeError
    ; unp                                   , R(unpt)
    ; unp'                                  , R(unp't)
    ; bunp                                  , TypeError
    (* SANITY CHECKS FOR HELPER CODE --- NOT PART OF GRADE *)
    (*
    ; _pidpair                               , R(_pidpairt)
    ; _weird1                                , R(_pidpairt)
    ; _weird2                                , R(_weird2t)
    ; _weird3                                , R(_weird3t)
    *)
    ]
  , infer_test_result
  , (=)
  , [%show : exp]
  , [%show : ty test_result]
  )

let _ = 
  _SHOW_PASSED_TESTS := false ;
  run_tests [step_tests;infer_tests] *)

(* Name: <your name> *)
