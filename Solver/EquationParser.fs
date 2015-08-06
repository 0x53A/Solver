[<AutoOpen>]
module EquationsParser

open Microsoft.FSharp.Quotations
open Microsoft.FSharp.Quotations.Patterns
open Microsoft.FSharp.Quotations.DerivedPatterns
open System
open MathNet.Numerics.LinearAlgebra
open System.Linq

module SM = 
    let Pow(x : 'a, y : 'b) : Variable = failwith "dummy"
    let Sqrt(x : 'a) : Variable = failwith "dummy"
    let Exp(x : 'a) : Variable = failwith "dummy"
    let Log(x : 'a) : Variable = failwith "dummy"
    let Sin(x : 'a) : Variable = failwith "dummy"
    let Cos(x : 'a) : Variable = failwith "dummy"
    // required because there are type issues if one side contains only a constant
    let C(x) : Variable = failwith "dummy"

let rec parseExpr expr =
 match expr with
    | SpecificCall <@@ (+) @@> (_, _, exprList) -> 
        let left = parseExpr exprList.Head
        let right = parseExpr exprList.Tail.Head
        Add(left, right)
    | SpecificCall <@@ (-) @@> (_, _, exprList) -> 
        let left = parseExpr exprList.Head
        let right = parseExpr exprList.Tail.Head
        Sub(left, right)
    | SpecificCall <@@ (*) @@> (_, _, exprList) -> 
        let left = parseExpr exprList.Head
        let right = parseExpr exprList.Tail.Head
        Mul(left, right)
    | SpecificCall <@@ (/) @@> (_, _, exprList) -> 
        let left = parseExpr exprList.Head
        let right = parseExpr exprList.Tail.Head
        Div(left, right)
    | SpecificCall <@@ SM.Pow @@> (_, _, exprList) -> 
        let left = parseExpr exprList.Head
        let right = parseExpr exprList.Tail.Head
        Pow(left, right)
    | SpecificCall <@@ SM.Sqrt @@> (_, _, exprList) -> 
        let arg = parseExpr exprList.Head
        Sqrt(arg)
    | SpecificCall <@@ SM.Exp @@> (_, _, exprList) -> 
        let arg = parseExpr exprList.Head
        Exp(arg)
    | SpecificCall <@@ SM.Log @@> (_, _, exprList) -> 
        let arg = parseExpr exprList.Head
        Log(arg)
    | SpecificCall <@@ SM.Sin @@> (_, _, exprList) -> 
        let arg = parseExpr exprList.Head
        Sin(arg)
    | SpecificCall <@@ SM.Cos @@> (_, _, exprList) -> 
        let arg = parseExpr exprList.Head
        Cos(arg)
    | SpecificCall <@@ SM.C @@> (_, _, exprList) -> 
        match exprList.Head with
        | Int32(n) -> Val(Const(float n))
        | Double(f) -> Val(Const f)
        | x -> failwith (sprintf "invalid constant: [%A]" x)
    | Int32(n) -> Val(Const(float n))
    | Double(f) -> Val(Const f)
    | Value(var, typ) when typ = typeof<Variable> -> 
        let variable = var :?> Variable
        Val(Value.Var(variable))
    | _ -> failwith (sprintf "not implemented:parseQuotation:%A" expr)


let parseQuotation quot : Equation =
    match quot with
    | SpecificCall <@@ (=) @@> (_, _, exprList) -> 
        let left = parseExpr exprList.Head
        let right = parseExpr exprList.Tail.Head
        Equation(Simplify left, Simplify right)
    | _ -> failwith "invalid"

