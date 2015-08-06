[<AutoOpen>]
module Equations

open System
open MathNet.Numerics.LinearAlgebra
open System.Collections.Generic

type Variable = 
    | Variable of string
    
    member self.Name = 
        let (Variable v) = self
        v
    
    // these dummy operators are required to enable the expressions
    static member (+) (a : Variable, b : Variable) : Variable = failwith "dummy"
    static member (+) (a, b : Variable) : Variable = failwith "dummy"
    static member (+) (a : Variable, b) : Variable = failwith "dummy"
    static member (-) (a : Variable, b : Variable) : Variable = failwith "dummy"
    static member (-) (a, b : Variable) : Variable = failwith "dummy"
    static member (-) (a : Variable, b) : Variable = failwith "dummy"
    static member (*) (a : Variable, b : Variable) : Variable = failwith "dummy"
    static member (*) (a, b : Variable) : Variable = failwith "dummy"
    static member (*) (a : Variable, b) : Variable = failwith "dummy"
    static member (/) (a : Variable, b : Variable) : Variable = failwith "dummy"
    static member (/) (a, b : Variable) : Variable = failwith "dummy"
    static member (/) (a : Variable, b) : Variable = failwith "dummy"

type Value = 
    | Var of Variable
    | Const of float

type Expression = 
    | Val of Value
    | Neg of Expression
    | Add of Expression * Expression
    | Sub of Expression * Expression
    | Mul of Expression * Expression
    | Div of Expression * Expression
    | Pow of Expression * Expression
    | Sqrt of Expression
    | Exp of Expression
    | Log of Expression
    | Sin of Expression
    | Cos of Expression

type Equation = 
    | Equation of Expression * Expression

let (|Op|_|) (x : Expression) = 
    match x with
    | Add(e1, e2) -> Some(Add, e1, e2)
    | Sub(e1, e2) -> Some(Sub, e1, e2)
    | Mul(e1, e2) -> Some(Mul, e1, e2)
    | Div(e1, e2) -> Some(Div, e1, e2)
    | Pow(e1, e2) -> Some(Pow, e1, e2)
    | _ -> None

let (|Func|_|) (x : Expression) = 
    match x with
    | Exp(e) -> Some(Exp, e)
    | Log(e) -> Some(Log, e)
    | Sin(e) -> Some(Sin, e)
    | Cos(e) -> Some(Cos, e)
    | Sqrt(e) -> Some(Sqrt, e)
    | _ -> None

/// matches a constant
let (|C|_|) (x : Expression) = 
    match x with
    | Val(Const(c)) -> Some(c)
    | _ -> None
    
/// matches a variable
let (|V|_|) (x : Expression) = 
    match x with
    | Val(Var(v)) -> Some(v)
    | _ -> None

/// matches neither constant nor variable
let (|NV|_|) (x : Expression) = 
    match x with
    | Val(_) -> None
    | _ -> Some(x)

let _const f = Val(Const(f))
let _val v = Val(Var(v))

let rec Simplify(x : Expression) : Expression = 
    match x with
    // -1 => Neg(1)
    //| (C(c)) when c < 0. -> Neg(Val(Const(-1. * c)))
    | Neg(C c) -> _const (-1. * c)
    | Add(C n1, C n2) -> _const(n1 + n2)
    | Sub(C n1, C n2) -> _const(n1 - n2)
    | Mul(C n1, C n2) -> _const(n1 * n2)
    | Div(C n1, C n2) -> _const(n1 / n2)
    | Pow(C c1, C c2) -> _const(Math.Pow(c1, c2))
    | Sqrt(C c) -> _const(Math.Sqrt c)
    | Exp(C c) -> _const(Math.Exp c)
    | Log(C c) -> _const(Math.Log c)
    | Sin(C c) -> _const(Math.Sin c)
    | Cos(C c) -> _const(Math.Cos c)
    | Neg(C 0.) -> _const(0.)
    | Neg(Neg(e)) -> e |> Simplify
    // -(a - b) => b - a
    | Neg(Sub(e1, e2)) -> Sub(e2, e1) |> Simplify
    | Add(e, Val(Const(0.))) -> e |> Simplify
    | Add(Val(Const(0.)), e) -> e |> Simplify
    | Add(Val(n), NV(e)) -> Add(e, Val(n)) |> Simplify
    | Add(e1, Neg(e2)) -> Sub(e1, e2) |> Simplify
    | Add(Neg(e1), e2) -> Sub(e2, e1) |> Simplify
    // (x + 1) + 2 => x + 3
    | Add(Add(e, Val(c1)), Val(c2)) -> Add(e, Add (Val c1, Val c2)) |> Simplify
    | Sub(e, C(0.)) -> e |> Simplify
    | Sub(C(0.), e) -> Neg(e) |> Simplify
    // a - (-b) => a + b
    | Sub(e1, Neg(e2)) -> Add(e1, e2) |> Simplify
    // (x - 1) - 2 => x - 3
    | Sub(Sub(e2, Val(c1)), Val(c2)) -> Sub(e2, Add (Val c1 , Val c2)) |> Simplify
    // 2 - (1 - x) => x + (2 - 1)
    | Sub(Val(c1), Sub(Val(c2), e)) -> Add(e, Sub(Val(c1), Val(c2))) |> Simplify
    | Mul(e, C(1.)) -> e |> Simplify
    | Mul(C(1.), e) -> e |> Simplify
    | Mul(e, C(0.)) -> Val(Const(0.))
    | Mul(C(0.), e) -> Val(Const(0.))
    //| Mul(NV(e), Val(n)) -> Mul(Val(n), e) |> Simplify
    | Mul(Div(Val(n), e1), e2) -> Mul(Val(n), Div(e2, e1)) |> Simplify
    //| Mul(e1, Div(Val(n), e2)) -> Mul(Val(n), Div(e1, e2)) |> Simplify
    | Mul(Neg(e1), e2) -> Neg(Mul(e1, e2)) |> Simplify
    | Mul(e1, Neg(e2)) -> Neg(Mul(e1, e2)) |> Simplify
    // 4 * (3 * x) => (3*4) * x
    | Mul(C(c1), Mul(C(c2), e)) -> Mul(_const(c1 * c2), e) |> Simplify
    | Div(C(0.), e) -> Val(Const(0.))
    | Div(e, C(1.)) -> e |> Simplify
    | Div(Neg(e1), e2) -> Neg(Div(e1, e2)) |> Simplify
    | Div(e1, Neg(e2)) -> Neg(Div(e1, e2)) |> Simplify
    | Pow(C(0.), e) -> _const (0.)
    | Pow(C(1.), e) -> _const (1.)
    | Pow(e, C(0.)) -> _const (1.)
    | Pow(e, C(1.)) -> e |> Simplify
    | Op(op, e1, e2) -> 
        let e1s = Simplify e1
        let e2s = Simplify e2
        if (e1, e2) <> (e1s, e2s) then op (e1s, e2s) |> Simplify
        else op (e1, e2)
    | Func(f, e) -> 
        let es = Simplify e
        if e <> es then f (es) |> Simplify
        else f (e)
    | _ -> x


let rec SimplifyZeroFinding (x : Expression) =
    match x with
    // 0 = -x   =>  0 = x 
    | Neg(e) -> e |> Simplify |> SimplifyZeroFinding
    // 0 = 5x   =>  0 = x
    | Mul(C _, e) | Mul(e, C _) -> e |> Simplify |> SimplifyZeroFinding
    // 0 = x/5  =>  0 = x
    | Div(e, C _) -> e |> Simplify |> SimplifyZeroFinding
    | _ ->
        let x' = x |> Simplify
        if x' = x then
            x
        else
            x' |> SimplifyZeroFinding


let rec FlattenExpressionTree expr = seq {
    yield expr
    match expr with
    | Neg x -> yield! FlattenExpressionTree x
    | Op(_, a, b) ->
        yield! FlattenExpressionTree a
        yield! FlattenExpressionTree b
    | Func(_, x) -> yield! FlattenExpressionTree x
    | _ -> ()
}

let ContainsExpression outer inner = outer |> FlattenExpressionTree |> Seq.exists (fun e -> e = inner)

let rec PartialDerivative (variable : Variable) (exp : Expression) : Expression = 
    let derivative = PartialDerivative variable
    let X = Val(Var(variable))
    
    /// matches the variable which is derived
    let (|X|_|) (a : Expression) = 
        match a with
        | V v when v = variable -> Some()
        | _ -> None
    
    /// matches a constant (or a variable not being derived -> should be treated like a constant)
    let (|N|_|) (a : Expression) =
        if ContainsExpression a (Val(Var variable)) then None
        else Some(a)
    
    let y = 
        match exp with
        // x => 1
        | X -> _const 1.
        // 12 => 0
        | N(_) -> _const (0.)
        // -x => - (x')
        | Neg(e) -> Neg(derivative (e))
        // a + b => a' + b'
        | Add(e1, e2) -> Add(derivative (e1), derivative (e2))
        // a - b => a' - b'
        | Sub(e1, e2) -> Sub(derivative (e1), derivative (e2))
        // a * b => (a' * b) + (a * b')
        | Mul(e1, e2) -> Add(Mul(derivative (e1), e2), Mul(e1, derivative (e2)))
        // x ^ c => c * x ^ (c - 1)
        | Pow(X, N(n)) -> Mul(n, Pow(X, Sub(n, _const (1.))))
        // c ^ x => log(c) * (c^x) * x'
        | Pow(N(n), e) -> Mul(Mul(Log(n), Pow(n, e)), derivative (e))
        // Sqrt(x) => (x^-2)' => -2 * x^-3
        | Sqrt(X) -> Mul(_const -2., Pow(X, _const -3.))
        // sqrt(e) => 1/(2 * sqrt(e)) * e'
        | Sqrt(e) -> Mul(Div(_const 1., Mul(_const 2., Sqrt e)), derivative e)
        // e^x => e^x
        | Exp(X) -> Exp(X)
        // log(x) => 1 / x
        | Log(X) -> Div(_const (1.), X)
        // sin(x) -> cos(x)
        | Sin(X) -> Cos(X)
        // cos(x) -> -(sin(x))
        | Cos(X) -> Neg(Sin(X))
        // 1 / x => x' / (x^2)
        | Div(C(1.), e) -> Div(derivative (e), Pow(e, _const (2.)))
        // Chain Rule
        | Func(g, f) ->
            let dg = derivative (g (X))
            let df = derivative (f)
            match dg with
            | Func(dgf, dge) -> Mul(dgf (f), df)
            | Op(op, e1, e2) -> Mul(op (e1, e2), df)
            | _ -> failwith (sprintf "Unable to match compound function [%A]" dg)
        // chain rule for div
        | Div(e1, e2) -> Div(Sub(Mul(derivative e1, e2), Mul(e1, derivative e2)), Pow(e2, _const 2.))
        // chain rule for pow: [e ^ c] => e ^ (c-1) * e'
        | Pow(e, N n) -> Mul(Mul(n, Pow(e, Sub(n, _const 1.))), derivative e)
        | _ -> failwith (sprintf "Unable to match expression [%A]" exp)
    
    Simplify y
    //y

(* Utility *)

let rec Replace (lookFor : Expression) (replaceWith : Expression) (original : Expression) : Expression = 
    let replace' = Replace lookFor replaceWith
    if original = lookFor then replaceWith
    else 
        match original with
        | Neg x -> Neg(replace' x)
        | Add(a, b) -> Add(replace' a, replace' b)
        | Sub(a, b) -> Sub(replace' a, replace' b)
        | Mul(a, b) -> Mul(replace' a, replace' b)
        | Div(a, b) -> Div(replace' a, replace' b)
        | Pow(a, b) -> Pow(replace' a, replace' b)
        | Exp x -> Exp(replace' x)
        | Log x -> Log(replace' x)
        | Sin x -> Sin(replace' x)
        | Cos x -> Cos(replace' x)
        | Sqrt x -> Sqrt(replace' x)
        | Val _ as x -> x

let ExtractAllVariables (exp : Expression) =
    let rec extract_r exp = seq {
        match exp with
            | Val(Var v) -> yield v
            | Neg x -> yield! extract_r x
            | Op(_, a, b) ->
                yield! extract_r a
                yield! extract_r b
            | Func(_, x) -> yield! extract_r x
            | _ -> ()
    }
    extract_r exp |> Seq.distinct |> Seq.cache


let rec Solve (variables : IDictionary<string, float>) (exp : Expression) : float =
    let solve = Solve variables
    match exp with        
        | Neg x -> -1. * (solve x)
        | Add(a, b) -> (solve a) + (solve b)
        | Sub(a, b) -> (solve a) - (solve b)
        | Mul(a, b) -> (solve a) * (solve b)
        | Div(a, b) -> (solve a) / (solve b)
        | Pow(a, b) -> Math.Pow(solve a, solve b)
        | Exp x -> Math.Exp(solve x)
        | Log x -> Math.Log(solve x)
        | Sin x -> Math.Sin(solve x)
        | Sqrt x -> Math.Sqrt(solve x)
        | Cos x -> Math.Cos(solve x)
        | Val(Const c) -> c
        | Val(Var v) -> variables.[v.Name]

(* Jacobi Matrix *)

let CreateDeriverateMatrix (exl : Expression list) (allVariables : Variable list) =
    let numVariables = allVariables.Length
    let numExpressions = exl.Length
    let derivates = Array2D.init numExpressions numVariables (fun m n -> PartialDerivative allVariables.[n] exl.[m])
    derivates

(* Formatting *)

let OpName(e : Expression) : string = 
    match e with
    | Add(e1, e2) -> "+"
    | Sub(e1, e2) -> "-"
    | Mul(e1, e2) -> "*"
    | Div(e1, e2) -> "/"
    | Pow(e1, e2) -> "^"
    | _ -> failwith (sprintf "Unrecognized operator [%A]" e)

let FuncName (e : Expression) (a : string) : string = 
    match e with
    | Exp(x) -> sprintf "e^(%s)" a
    | Log(x) -> sprintf "log(%s)" a
    | Sin(x) -> sprintf "sin(%s)" a
    | Cos(x) -> sprintf "cos(%s)" a
    | Sqrt(x) -> sprintf "sqrt(%s)" a
    | _ -> failwith (sprintf "Unrecognized function [%A]" e)

let FormatExpression x = 
    let rec FormatSubExpression(outer : Expression option, inner : Expression) : string = 
        match inner with
        | V(Variable var) -> sprintf "%s" var
        | C(n) -> sprintf "%g" n
        | Neg x -> sprintf "-%s" (FormatSubExpression(Some(inner), x))
        | Op(op, e1, e2) -> 
            let s = 
                FormatSubExpression(Some(inner), e1) + " " + OpName(inner) + " " + FormatSubExpression(Some(inner), e2)
            match outer with
            | None -> s
            | _ -> "(" + s + ")"
        | Func(f, e) -> FuncName (inner) (FormatSubExpression(None, e))
        | _ -> failwith "nyi"
    FormatSubExpression(None, x)
    
#nowarn "0060"
type Expression with
     override x.ToString() = FormatExpression x