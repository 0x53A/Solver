[<AutoOpen>]
module Graph

open System.Collections.Generic
open System


type StructuralDictionary<'TKey, 'TValue when 'TKey : equality and 'TKey : comparison and 'TValue : equality and 'TValue : comparison>() =
    inherit Dictionary<'TKey, 'TValue>()
    new (other:IDictionary<'TKey, 'TValue>) as this =
        StructuralDictionary()
        then
            for x in other do this.Add (x.Key, x.Value)
    override a.Equals other =
        if other = null then false
        else if not (other :? Dictionary<'TKey, 'TValue>) then false
        else
            let b = other :?> Dictionary<'TKey, 'TValue>
            if b.Count <> a.Count then false
            else if (set a.Keys) <> (set b.Keys) then
                false
            else if a |> Seq.exists (fun kv -> kv.Value <> b.[kv.Key]) then
                false
            else
                true
    override self.GetHashCode() = self.Count //TODO
    interface IEquatable<IReadOnlyDictionary<'TKey, 'TValue>> with
        member self.Equals other = self.Equals (other :> obj)
    interface IComparable<StructuralDictionary<'TKey, 'TValue>> with
        member self.CompareTo other =
            if self.Count <> other.Count then
                self.Count.CompareTo other.Count
            else
                let (keysA, keysB) = (set self.Keys), (set other.Keys)
                if keysA <> keysB then
                    (keysA :> IComparable).CompareTo keysB
                else
                    let diff = Seq.zip self other |> Seq.tryFind (fun (s,o) -> s <> o)
                    if diff.IsSome then
                        let (s,o) = diff.Value
                        compare s.Value o.Value
                    else 0
    interface IComparable with
        member self.CompareTo other =
            if other :? StructuralDictionary<'TKey, 'TValue> then
                let otherDict = other :?> StructuralDictionary<'TKey, 'TValue>
                (self :> IComparable<StructuralDictionary<'TKey, 'TValue>>).CompareTo otherDict
            else
                1

type Graph<'a when 'a : comparison> = StructuralDictionary<'a, Set<'a>>

let toStructuralDict kv =
    let d = StructuralDictionary()
    for (k,v) in kv do d.Add(k, v)
    d 

let kvToDict (kvSeq:KeyValuePair<'a, 'b> seq) = kvSeq |> Seq.map (fun kv -> kv.Key, kv.Value) |> toStructuralDict

let graphFromVariablesListings (vars : #seq<#seq<'a>>) =
    let connections = seq {
            for x in vars do
                for y in x do
                    for z in x do
                        yield (y,z)
                        yield (z,y)
        }
    let groups = connections |> Seq.distinct |> Seq.groupBy fst |> Seq.map (fun (x,y) -> x,(y|>Seq.map snd|>set)) |> toStructuralDict
    groups


let graphFromExpressions expressions =
    expressions |> List.map ExtractAllVariables |> graphFromVariablesListings

let partitionByBool (func : 'a -> bool) (elements : 'a list) =
    let rec partitionByBool_r elements l_true l_false =
        match elements with
        | [] -> (l_true |> List.rev, l_false |> List.rev)
        | head :: tail ->
            match func head with
            | true -> partitionByBool_r tail (head :: l_true) (l_false)
            | false -> partitionByBool_r tail (l_true) (head :: l_false)
    partitionByBool_r elements [] []

let rec getSubGraphs (graph : StructuralDictionary<'a, Set<'a>>) =
    match graph.Count with
    | 0 -> Set([])
    | 1 -> [ graph ] |> set
    | _ ->
        let allVariables = graph.Keys |> set
        let nodeList = graph |> Seq.toList
        // start with the first node, and recursively get all referenced nodes
        let first = nodeList.Head

        let rec getRecursive currentSet =
            let newSet = currentSet |> Seq.collect (fun x -> graph.[x]) |> set
            if newSet = currentSet then
                currentSet
            else
                getRecursive newSet

        let dependenciesOfFirst = getRecursive (Set.add first.Key first.Value)
        if allVariables = dependenciesOfFirst then
            [ graph ] |> set
        else
            let (firstSubGraph, notFirstSubGraph) = nodeList |> partitionByBool (fun kv -> dependenciesOfFirst.Contains kv.Key)
            Set.add (firstSubGraph |> kvToDict) (getSubGraphs (notFirstSubGraph |> kvToDict))