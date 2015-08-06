module MainApp

open System
open System.Windows
open System.Windows.Controls
open System.Windows.Markup
open System.IO


let loadWindow() =
   let window = XamlReader.Parse(File.ReadAllText "MainView.xaml") :?> Window
   window

[<STAThread>]
(new Application()).Run(loadWindow()) |> ignore

