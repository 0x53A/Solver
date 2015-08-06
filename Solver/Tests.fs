
namespace Tests


open Microsoft.VisualStudio.TestTools.UnitTesting
open System

type ExpressionResult =
| Result of float
| Exception

[<AutoOpen>]
module TestInternal =
    open System

    let trySolve vars expr =
        try
            Result (Solve vars expr)
        with
        | :? System.DivideByZeroException -> ExpressionResult.Exception

    let compareExpressions epsilon a b =
        let variables = (ExtractAllVariables a |> set) + (ExtractAllVariables b |> set)
        let rounds = 1000
        let rnd = Random(0)
        { 0 .. rounds } |> Seq.exists (fun _ -> 
            let varDict = variables |> Seq.map (fun v -> (v.Name, rnd.NextDouble() * 10000.)) |> dict
            match (trySolve varDict a, trySolve varDict b) with
            | (Exception, Exception) -> false
            | (Result r1, Result r2) when Math.Abs(r1 - r2) > epsilon -> false
            | _ -> true
          )
        
        
    let testExpressions epsilon expressions initialValues =

        let (nIterations, result) = Solver.run 10000 expressions initialValues
        let error = 
            expressions
            |> Seq.map (fun x -> x |> Solve result |> Math.Abs)
        let maxError = error |> Seq.max
        if maxError > epsilon then Assert.Fail(sprintf "max absolute Error: %g > %g" maxError epsilon)

    let testConstraints epsilon constraints initialValues =
   
        let expressions = 
            constraints
            |> List.collect ConstraintsToQuotations
            |> List.map parseQuotation
            |> List.map (fun (Equation(l, r)) -> Sub(l, r) |> Simplify)

        testExpressions epsilon expressions initialValues


[<TestClass>]
type DerivateTests() =

    [<TestMethod>]
    member self.``derive sqrt(x^2 + 1)``() =
        let x = Variable "x"
        let expected = parseExpr <@ x / SM.Sqrt(SM.Pow(x,2)+1) @>
        let result = PartialDerivative x (parseExpr <@ SM.Sqrt(SM.Pow(x,2) + 1) @>)
        Assert.IsTrue (compareExpressions 1e-20 expected result)

        
    [<TestMethod>]
    member self.``derive sqrt(x^2 + 1) == derive (x^2 + 1)^0.5``() =
        let x = Variable "x"
        let a = PartialDerivative x (parseExpr <@ SM.Pow(SM.Pow(x,2) + 1, 0.5) @>)
        let b = PartialDerivative x (parseExpr <@ SM.Sqrt(SM.Pow(x,2) + 1) @>)
        Assert.IsTrue (compareExpressions 1e-20 a b)
        
[<TestClass>]
type SolverTests() =

    [<TestMethod>]
    member self.``solving simple equations``() =

        let x = Variable "x"
        let y = Variable "y"
        let a = Variable "a"
        let b = Variable "b"
    
        let initialValues = 
            [ "x", 1.
              "y", 1.
              "a", -1.
              "b", 1.
              "e", 1.
              "f", 1. ]
            |> toStructuralDict
    
        let systems = 
            [ [ <@ 4 * SM.Pow(x, 2) - SM.Pow(y, 3) + 28 = SM.C 0 @>
                <@ 3 * SM.Pow(x, 3) + 4 * SM.Pow(y, 2) - 145 = SM.C 0 @> ]
              [ <@ x = SM.C 0 @>
                <@ y = SM.C 0 @>
                <@ a = x @>
                <@ SM.Sqrt(SM.C 1000) = SM.Sqrt(SM.Pow(a - x, 2) + SM.Pow(b - y, 2)) @> ] ]
    
        for equations in systems do
        
            let expressions = 
                equations
                |> List.map parseQuotation
                |> List.map (fun eq -> 
                       let (Equation(l, r)) = eq
                       Sub(l, r) |> Simplify)

            testExpressions 1e-20 expressions initialValues
        

        
[<TestClass>]
type GraphTests() =
    [<TestMethod>]
    member self.``empy graph``() =
        let subgraphs = [] |> toStructuralDict |> getSubGraphs
        let areTheyEqual = (subgraphs = Set [])
        Assert.IsTrue areTheyEqual
        
    [<TestMethod>]
    member self.``single graph``() =
        let graph = ["a", ["a"] |> set ] |> toStructuralDict
        let subgraphs = graph |> getSubGraphs
        let areTheyEqual = (subgraphs = (set [ graph ]))
        Assert.IsTrue areTheyEqual
        
    [<TestMethod>]
    member self.toStructuralDict() =
        Assert.IsTrue( ([1,2]|> toStructuralDict) = ([1,2]|> toStructuralDict))

    [<TestMethod>]
    member self.``complex graph``() =
        let graph = [ [1;2;3] ; [2;3;4] ; [4;5;6] ; [7;8;9] ; [9;10] ] |> graphFromVariablesListings
        let subgraphs = graph |> getSubGraphs
        let expectedSubGraphs = [ [1;2;3] ; [2;3;4] ; [4;5;6] ] :: [ [7;8;9] ; [9;10] ] :: [] |> List.map graphFromVariablesListings |> set
        let areTheyEqual = (subgraphs = expectedSubGraphs)
        Assert.IsTrue areTheyEqual
        
[<TestClass>]
type ConstraintTests() =
    [<TestMethod>]
    member self.``simple rectangular constraints``() =
    
        let p1 = Point(Variable "x1", Variable "y1")
        let p2 = Point(Variable "x2", Variable "y2")
        let p3 = Point(Variable "x3", Variable "y3")
        let p4 = Point(Variable "x4", Variable "y4")
        let l1 = Line(p1, p2)
        let l2 = Line(p2, p3)
        let l3 = Line(p3, p4)
        let l4 = Line(p4, p1)

        let initialValues = 
            [   "x1", 0.5
                "y1", 0.5
                "x2", 0.5
                "y2", 1.6
                "x3", 1.6
                "y3", 1.6
                "x4", 1.4
                "y4", 1.4]  
            |> toStructuralDict
           
        let constraints = 
            [
                FixedValue(p1.X, 0.)
                FixedValue(p1.Y, 0.)
    
                HorizontalOffset(l1, 0.)
                HorizontalOffset(l2, 5.) 
                HorizontalOffset(l3, 0.)
                HorizontalOffset(l4, -5.)
    
                VerticalOffset(l1, 10.)
                VerticalOffset(l2, 0.) 
                VerticalOffset(l3, -10.)
                VerticalOffset(l4, 0.)
              ]
        
        testConstraints 1e-20 constraints initialValues


        
    [<TestMethod>]
    member self.``constrained triangle with angle``() =
        
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
                "cy", 7. ] |> toStructuralDict
                
        testConstraints 1e-20 constraints initialValues

