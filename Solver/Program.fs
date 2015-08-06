open Microsoft.FSharp.Quotations
open Microsoft.FSharp.Quotations.Patterns
open Microsoft.FSharp.Quotations.DerivedPatterns
open System
open MathNet.Numerics.LinearAlgebra
open System.Linq
open System.Collections
open System.Collections.Generic

let solveExpressionsWithPrettyPrinting expressions initialValues =

    printfn "======Expressions====="
    expressions |> Seq.iteri (fun i e -> printfn "[%i] 0 = %s" i (e.ToString()))

    let (usedIterations, result) = Solver.run 10000 expressions initialValues

    printfn "======Result====="
    printfn "used iterations: %i" usedIterations
    result |> Seq.iter (printfn "%A")
    printfn "======Error====="
    expressions |> Seq.iteri (fun i e -> e |> Solve result |> (printfn "[%i] %A" i))


let solveConstraintsWithPrettyPrinting constraints initialValues =
   
    let expressions = 
        constraints
        |> List.collect ConstraintsToQuotations
        |> List.map parseQuotation
        |> List.map (fun (Equation(l, r)) -> Sub(l, r) |> Simplify)

    solveExpressionsWithPrettyPrinting expressions initialValues

// define some physical constants
[<Literal>]
let Alpha = 2
[<Literal>]
let Beta = 2
[<Literal>]
let Gamma = 5

let plus = (+)

/// overloaded plus operator for physical types
let (+) x y = match (x,y) with | (Alpha,Beta) -> Gamma | (gamma, omega) -> plus gamma omega

printfn "%i" (2 + 2)
printfn "%i" (1 + 3)
printfn "%i" ((1+1) + (2*1))


[<EntryPoint>]
let main argv = 
    
    let l1 = Line(Point(Variable "ax", Variable "ay"), Point(Variable "bx", Variable "by"))
    let l2 = Line(Point(Variable "ax", Variable "ay"), Point(Variable "cx", Variable "cy"))

    let constraints = 
        [
            FixedValue(Variable("ax"), 0.)
            FixedValue(Variable("ay"), 0.)
            
            HorizontalDistance(l1, 0.)
            VerticalOffset(l1, 20.)

            VerticalOffset(l2, 10.)

            Angle(l1, l2, 45.)
        ]

    
    let initialValues = 
        [   "ax", 1.
            "ay", 1.
            "bx", 50.
            "by", -2.
            "cx", 64.
            "cy", 7. ]


    ///
    let expressions = 
        constraints
        |> List.collect ConstraintsToQuotations
        |> List.map parseQuotation
        |> List.map (fun (Equation(l, r)) -> Sub(l, r) |> SimplifyZeroFinding)

    let ctx = { Expressions = expressions
                Constants = []
                Dependants = []
               }
    let simplified = ctx |> SimplifyEquationsByGraph
    /////////////////


    solveConstraintsWithPrettyPrinting constraints (initialValues |> toStructuralDict)
    0 // return an integer exit code
