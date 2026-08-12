/-
# Uwueave.Preo.Elab -- public preoscript command facade

The implementation is split into phase modules under `Uwueave.Preo.Elab` so
Lean compiles bounded command workers instead of one monolithic elaborator.
This module owns the single public registration for each surface command.
-/
import Uwueave.Preo.Elab.Declaration
import Uwueave.Preo.Elab.Certificate
import Uwueave.Preo.Elab.Budget
import Uwueave.Preo.Elab.Export
import Uwueave.Preo.Elab.Report

namespace Uwueave.Preo

open Lean Elab Command

@[command_elab preoDecl]
def elabPreoDecl : CommandElab :=
  Uwueave.Preo.Elab.Declaration.elabPreoDeclCore

@[command_elab preoCertificate]
def elabPreoCertificate : CommandElab :=
  Uwueave.Preo.Elab.Certificate.elabPreoCertificateCore

@[command_elab preoBudget]
def elabPreoBudget : CommandElab :=
  Uwueave.Preo.Elab.Budget.elabPreoBudgetCore

@[command_elab preoExport]
def elabPreoExport : CommandElab :=
  Uwueave.Preo.Elab.Export.elabPreoExportCore

@[command_elab preoReport]
def elabPreoReport : CommandElab :=
  Uwueave.Preo.Elab.Report.elabPreoReportCore

namespace ProtocolSurface

@[command_elab preoProtocolCommand]
def elabNativeProtocol : CommandElab := elabNativeProtocolCore

end ProtocolSurface

end Uwueave.Preo
