[<AutoOpen>]
module Constraints

open Microsoft.FSharp.Quotations
open System

type Point = 
    | Point of x : Variable * y : Variable
    
    member self.X = 
        let (Point(x, _)) = self
        x
    
    member self.Y = 
        let (Point(_, y)) = self
        y

type Line = 
    | Line of Point * Point

type Constraint = 
    | PointEqual of Point * Point
    | PointCenterOfLine of Line * Point
    | Angle of Line * Line * degree : float
    | EquiDistant of Line * Line
    | FixedDistance of Line * float
    | PointOnCutOfLines of Line * Line * Point
    | FixedValue of Variable * float
    | HorizontalDistance of Line * float
    | VerticalDistance of Line * float
    | HorizontalOffset of Line * float
    | VerticalOffset of Line * float

let ConstraintsToQuotations(eq : Constraint) : Expr list = 
    match eq with
    | PointEqual(Point(ax, ay), Point(bx, by)) -> 
        [ <@ ax = bx @>
          <@ ay = by @> ]
    | PointCenterOfLine(Line(Point(ax, ay), Point(bx, by)), Point(cx, cy)) -> 
        [ <@ cx = (ax + bx) / 2 @>
          <@ cy = (ay + by) / 2 @> ]
    | Angle(Line(Point(ax, ay), Point(bx, by)), Line(Point(cx, cy), Point(dx, dy)), degree) -> 
        let v1x = <@ bx - ax @>
        let v1y = <@ by - ay @>
        let v2x = <@ dx - cx @>
        let v2y = <@ dy - cy @>
        match degree with
        | 270. | -90. | -270. | 90. -> [ <@ SM.C 0 = %v1x * %v2x + %v1y * %v2y @> ]
        | 0. -> [ <@ %v1x * %v2y = %v1y * %v2x @> ]
        | _ -> 
            let cosPhi = Math.Cos(degree)
            let innerProduct = <@ %v1x * %v2x + %v1y * %v2y @>
            let lengthV1 = <@ SM.Sqrt(SM.Pow(%v1x, 2) + SM.Pow(%v1y, 2)) @>
            let lengthV2 = <@ SM.Sqrt(SM.Pow(%v2x, 2) + SM.Pow(%v2y, 2)) @>
            [ <@ SM.C cosPhi = %innerProduct / (%lengthV1 * %lengthV2) @> ]
    | EquiDistant(Line(Point(ax, ay), Point(bx, by)), Line(Point(cx, cy), Point(dx, dy))) -> 
        let v1x = <@ bx - ax @>
        let v1y = <@ by - ay @>
        let v2x = <@ dx - cx @>
        let v2y = <@ dy - cy @>
        let innerProduct = <@ %v1x * %v2x + %v1y * %v2y @>
        let lengthV1 = <@ SM.Sqrt(SM.Pow(%v1x, 2) + SM.Pow(%v1y, 2)) @>
        let lengthV2 = <@ SM.Sqrt(SM.Pow(%v2x, 2) + SM.Pow(%v2y, 2)) @>
        [ <@ %lengthV1 = %lengthV2 @> ]
    | FixedDistance(Line(Point(ax, ay), Point(bx, by)), length) -> 
        let lengthSquared = length * length
        [ <@ SM.C lengthSquared = SM.Pow(bx - ax, 2) + SM.Pow(by - ay, 2) @> ]
    | PointOnCutOfLines(Line(Point(ax, ay), Point(bx, by)), Line(Point(cx, cy), Point(dx, dy)), Point(ex, ey)) -> 
        // steigung g1
        let t_g1 = <@ (by - ay) / (bx - ax) @>
        //  x where y = 0 for g1
        let null_g1 = <@ ax - ay / %t_g1 @>
        // steigung g2
        let t_g2 = <@ (dy - cy) / (dx - cx) @>
        //  x where y = 0 for g2
        let null_g2 = <@ cx - cy / %t_g1 @>
        [ // y = (x - null_g1) * t_g1
              // y = (x - null_g2) * t_g2
              // set y of both geraden equal
          <@ (ex - %null_g1) * %t_g1 = (ex - %null_g2) * %t_g2 @>
          <@ // calc y
             ey = (ex - %null_g1) * %t_g1 @> ]
    | FixedValue(var, value) -> [ <@ var = SM.C value @> ]
    | HorizontalDistance(Line(Point(ax, ay), Point(bx, by)), distance) -> 
        if distance = 0. then [ <@ ax = bx @> ]
        else [ <@ SM.Sqrt(SM.Pow(ax - bx, 2)) = SM.C distance @> ]
    | VerticalDistance(Line(Point(ax, ay), Point(bx, by)), distance) -> 
        if distance = 0. then [ <@ ay = by @> ]
        else [ <@ SM.Sqrt(SM.Pow(ax - bx, 2)) = SM.C distance @> ]
    | HorizontalOffset(Line(Point(ax, ay), Point(bx, by)), distance) ->
        [ <@ bx - ax = SM.C distance @> ]
    | VerticalOffset(Line(Point(ax, ay), Point(bx, by)), distance) -> 
        [ <@ by - ay = SM.C distance @> ]
