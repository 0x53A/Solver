[<AutoOpen>]
module Solver

open Microsoft.FSharp.Quotations
open Microsoft.FSharp.Quotations.Patterns
open Microsoft.FSharp.Quotations.DerivedPatterns
open System
open MathNet.Numerics.LinearAlgebra
open System.Linq
open System.Collections
open System.Collections.Generic

type SolverContext = {
    Expressions : Expression list
    Constants : (Variable * float) list
    Dependants : (Variable * Expression) list
}

let rec findConstant =
    function
    // v = c   =>   0 = v - c
    | Sub(V v, C c)
    // v = c   =>   0 = c - v
    | Sub(C c, V v) -> Some(v, c)
    // x = 0   =>   0 = x
    | V v -> Some(v, 0.)
    | _ -> None
    
let findDirectDependant =
    function
    | Sub(e, V v)
    | Sub(V v, e) when not (ContainsExpression e (Val(Value.Var v))) -> Some(v, e)
    | Add(e, V v)
    | Add(V v, e) when not (ContainsExpression e (Val(Value.Var v))) -> Some(v, Neg e)
    | _ -> None

let rec SimplifyEquationsByGraph (context:SolverContext) =

    let replaceConstants ctx =
        match ctx.Expressions |> List.tryPick findConstant with
        | Some(v, c) ->
            { ctx with
                Expressions = ctx.Expressions |> List.map ((Replace (Val(Value.Var v)) ((Val(Const c)))) >> SimplifyZeroFinding)
                Constants = (v,c) :: ctx.Constants
            }
        | None -> ctx

    let replaceDirectDependant ctx =
        match ctx.Expressions |> List.tryPick findDirectDependant with
        | Some(v, e) ->
            { ctx with
                Expressions = ctx.Expressions |> List.map ((Replace (Val(Value.Var v)) e) >> SimplifyZeroFinding)
                Dependants = (v, e) :: ctx.Dependants
            }
        | None -> ctx

    let rec runWhileChanging f arg =
        let arg' = f arg
        if arg' = arg then arg
        else runWhileChanging f arg'

    let pipeline = (runWhileChanging replaceConstants) >> (runWhileChanging replaceDirectDependant) 
    context |> runWhileChanging pipeline

    



//type IterationResult =
//| Perfect of nIteration : int * results : IDictionary<string,float>
//| Acceptable of nIteration : int * results : IDictionary<string,float> * error : float
//| Bad of nIteration : int * results : IDictionary<string,float> * error : float

let run maxIterations expressions initialValues =
    let allVariables = 
        expressions
        |> Seq.collect ExtractAllVariables
        |> Seq.distinct
        |> Seq.toList
    
    let jacobiMatrix = CreateDeriverateMatrix expressions allVariables
    
    printfn "======Jacobi======"
    jacobiMatrix |> Array2D.iteri (fun x y e -> printfn "[%i,%i] f(%s) = %s" x y (allVariables.[y].Name) (e.ToString()))

    let rec iterate iIteration maxIterations previousValues = 
        let valueMatrix = 
            jacobiMatrix
            |> Array2D.map (Solve previousValues)
            |> Matrix<float>.Build.DenseOfArray
        
        let invertedMatrix = MathNet.Numerics.LinearAlgebra.Double.ExtensionMethods.PseudoInverse valueMatrix
        let oldValueVector = vector (allVariables |> List.map (fun x -> previousValues.[x.Name]))
        let newValueVector = oldValueVector - invertedMatrix * (vector (expressions |> List.map (Solve previousValues)))
        
        let newValsDict = 
            newValueVector
            |> Seq.mapi (fun i v -> (allVariables.[i].Name, v))
            |> toStructuralDict
            
        let error = 
            expressions
            |> Seq.map (Solve newValsDict >> Math.Abs)

        if newValsDict = previousValues then (iIteration, newValsDict)
        else if expressions
                |> Seq.map (Solve newValsDict)
                |> (Seq.exists (fun f -> Math.Abs(f) > Double.Epsilon))
                |> not
        then (iIteration, newValsDict)
        else if iIteration > maxIterations then (Int32.MaxValue, newValsDict)
        else iterate (iIteration + 1) maxIterations newValsDict

    iterate 0 maxIterations initialValues
