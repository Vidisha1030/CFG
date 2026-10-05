/**
 * @license
 * SPDX-License-Identifier: Apache-2.0
 */

import React, { useState, useEffect, useRef, useMemo } from 'react';

const EPSILON = "ε";

interface GrammarDetails {
  unitProductionsRemoved?: number;
  chains?: string[];
  generating?: string[];
  nonGenerating?: string[];
  reachable?: string[];
  unreachable?: string[];
  nullable?: string[];
  generatedAlternatives?: number;
  preservedStartEpsilon?: boolean;
  passes?: number;
  stable?: boolean;
  finalProblems?: {
    uselessFree: boolean;
    epsilonFree: boolean;
    unitFree: boolean;
    epsilonProductions: string[];
    unitProductions: string[];
  };
}

interface StepInfo {
  grammar: Map<string, Set<string>>;
  details: GrammarDetails;
}

interface IterationRecord {
  pass: number;
  before: Map<string, Set<string>>;
  unit: Map<string, Set<string>>;
  useless: Map<string, Set<string>>;
  epsilon: Map<string, Set<string>>;
  unitInfo: StepInfo;
  uselessInfo: StepInfo;
  epsilonInfo: StepInfo;
  changed: boolean;
}

interface LastRunData {
  raw: Map<string, Set<string>>;
  unit: Map<string, Set<string>>;
  useless: Map<string, Set<string>>;
  epsilon: Map<string, Set<string>>;
  final: Map<string, Set<string>>;
  unitInfo: StepInfo;
  uselessInfo: StepInfo;
  epsilonInfo: StepInfo;
  iterations: IterationRecord[];
}

const examples: Record<string, string> = {
  basic: `S -> AB | a
A -> a | ε
B -> b | A
C -> c
D -> E
E -> D`,

  epsilon: `S -> ABC | a
A -> ε
B -> b | ε
C -> c`,

  unit: `S -> A
A -> B | a
B -> C
C -> D | c
D -> d`,

  useless: `S -> A | b
A -> a
B -> C
C -> B
D -> d`,

  complex: `S -> AB | BC | a
A -> aA | ε
B -> bB | C
C -> c | ε
D -> E
E -> D
F -> f`
};

/* =========================================================
   GRAMMAR UTILITIES
   ========================================================= */

function isVariable(s: string): boolean {
  return /^[A-Z][A-Z0-9_]*$/.test(s);
}

function cloneGrammar(g: Map<string, Set<string>>): Map<string, Set<string>> {
  const out = new Map<string, Set<string>>();
  for (const [lhs, set] of g) {
    out.set(lhs, new Set(set));
  }
  return out;
}

function rhsSymbols(rhs: string): string[] {
  if (rhs === EPSILON || rhs === "ε" || rhs === "epsilon" || rhs === "e") return [];
  return rhs.includes(" ")
    ? rhs.split(/\s+/).filter(Boolean)
    : [...rhs];
}

function symbolsToRhs(symbols: string[]): string {
  return symbols.length ? symbols.join("") : EPSILON;
}

function parseRHS(value: string): string {
  const s = value.trim();
  if (!s || s === EPSILON || /^epsilon$/i.test(s) || s === "e") {
    return EPSILON;
  }
  return /\s/.test(s)
    ? s.split(/\s+/).filter(Boolean).join(" ")
    : [...s].join("");
}

function parseCFG(text: string): Map<string, Set<string>> {
  if (!text.trim()) {
    throw new Error("Please enter a CFG before processing.");
  }

  const grammar = new Map<string, Set<string>>();
  const lines = text.split(/\r?\n/);

  lines.forEach((raw, index) => {
    const line = raw.trim();
    if (!line) return;

    const unicode = line.indexOf("→");
    const ascii = line.indexOf("->");
    const pos = ascii >= 0 ? ascii : unicode;
    const len = ascii >= 0 ? 2 : 1;

    if (pos < 0) {
      throw new Error(`Line ${index + 1}: Invalid production format. Use A -> B | a`);
    }

    const lhs = line.slice(0, pos).trim();
    const rhsText = line.slice(pos + len).trim();

    if (!/^[A-Z][A-Z0-9_]*$/.test(lhs)) {
      throw new Error(`Line ${index + 1}: "${lhs}" is not a valid variable.`);
    }

    if (!rhsText) {
      throw new Error(`Line ${index + 1}: Missing right-hand side.`);
    }

    if (!grammar.has(lhs)) {
      grammar.set(lhs, new Set());
    }

    rhsText.split("|").forEach(x => {
      grammar.get(lhs)!.add(parseRHS(x));
    });
  });

  if (!grammar.size) {
    throw new Error("No productions were found.");
  }

  return grammar;
}

function collectVariables(g: Map<string, Set<string>>): Set<string> {
  const vars = new Set(g.keys());
  for (const set of g.values()) {
    for (const rhs of set) {
      for (const s of rhsSymbols(rhs)) {
        if (isVariable(s)) {
          vars.add(s);
        }
      }
    }
  }
  return vars;
}

function countProductions(g: Map<string, Set<string>>): number {
  return [...g.values()].reduce((n, set) => n + set.size, 0);
}

function formatGrammar(g: Map<string, Set<string>>): string {
  if (!g.size) {
    return "∅";
  }

  return [...g.entries()]
    .map(([lhs, set]) => {
      const rhs = [...set].sort((a, b) => {
        if (a === EPSILON || a === "ε") return 1;
        if (b === EPSILON || b === "ε") return -1;
        return a.localeCompare(b);
      });
      return `${lhs} → ${rhs.join(" | ")}`;
    })
    .join("\n");
}

/**
 * Ensures that the final grammar has ABSOLUTELY NO EPSILON SIGN ("ε").
 * Any epsilon RHS is removed. If a variable is left with no rules, it is deleted.
 */
function removeEpsilonFromGrammar(g: Map<string, Set<string>>): Map<string, Set<string>> {
  const result = new Map<string, Set<string>>();
  for (const [lhs, set] of g) {
    const kept = new Set<string>();
    for (const rhs of set) {
      if (rhs !== EPSILON && rhs !== "ε" && rhs.toLowerCase() !== "epsilon" && rhs !== "") {
        kept.add(rhs);
      }
    }
    if (kept.size > 0) {
      result.set(lhs, kept);
    }
  }
  return result;
}

/* =========================================================
   STEP 1: USELESS SYMBOL ELIMINATION
   ========================================================= */

function eliminateUseless(g: Map<string, Set<string>>): StepInfo {
  const allVars = collectVariables(g);
  const generating = new Set<string>();
  let changed = true;

  while (changed) {
    changed = false;
    for (const [lhs, set] of g) {
      if (generating.has(lhs)) continue;
      for (const rhs of set) {
        const syms = rhsSymbols(rhs);
        if (
          rhs === EPSILON ||
          rhs === "ε" ||
          syms.every(s => !isVariable(s) || generating.has(s))
        ) {
          generating.add(lhs);
          changed = true;
          break;
        }
      }
    }
  }

  const nonGenerating = [...allVars].filter(v => !generating.has(v));

  // Keep generating variables and productions
  const gen = new Map<string, Set<string>>();
  for (const [lhs, set] of g) {
    if (!generating.has(lhs)) continue;
    const kept = new Set<string>();
    for (const rhs of set) {
      if (
        rhs === EPSILON ||
        rhs === "ε" ||
        rhsSymbols(rhs).every(s => !isVariable(s) || generating.has(s))
      ) {
        kept.add(rhs);
      }
    }
    if (kept.size) {
      gen.set(lhs, kept);
    }
  }

  // Find reachable variables
  const start = g.keys().next().value;
  const reachable = new Set<string>();
  const queue: string[] = [];

  if (start && gen.has(start)) {
    reachable.add(start);
    queue.push(start);
  }

  while (queue.length) {
    const lhs = queue.shift()!;
    for (const rhs of gen.get(lhs) || []) {
      for (const s of rhsSymbols(rhs)) {
        if (isVariable(s) && gen.has(s) && !reachable.has(s)) {
          reachable.add(s);
          queue.push(s);
        }
      }
    }
  }

  const unreachable = [...gen.keys()].filter(v => !reachable.has(v));

  // Keep reachable variables
  const result = new Map<string, Set<string>>();
  for (const [lhs, set] of gen) {
    if (!reachable.has(lhs)) continue;
    const kept = new Set<string>();
    for (const rhs of set) {
      if (
        rhs === EPSILON ||
        rhs === "ε" ||
        rhsSymbols(rhs).every(s => !isVariable(s) || reachable.has(s))
      ) {
        kept.add(rhs);
      }
    }
    if (kept.size) {
      result.set(lhs, kept);
    }
  }

  return {
    grammar: result,
    details: {
      generating: [...generating],
      nonGenerating,
      reachable: [...reachable],
      unreachable
    }
  };
}

/* =========================================================
   STEP 2: EPSILON PRODUCTION ELIMINATION
   ========================================================= */

function eliminateEpsilon(g: Map<string, Set<string>>): StepInfo {
  const result = new Map<string, Set<string>>(
    [...g.keys()].map(k => [k, new Set<string>()])
  );
  const nullable = new Set<string>();
  let generatedAlternatives = 0;

  let changed = true;
  while (changed) {
    changed = false;
    for (const [lhs, set] of g) {
      if (nullable.has(lhs)) continue;
      for (const rhs of set) {
        const syms = rhsSymbols(rhs);
        if (
          rhs === EPSILON ||
          rhs === "ε" ||
          (syms.length > 0 && syms.every(s => isVariable(s) && nullable.has(s)))
        ) {
          nullable.add(lhs);
          changed = true;
          break;
        }
      }
    }
  }

  for (const [lhs, set] of g) {
    for (const rhs of set) {
      // Do not copy epsilon
      if (rhs === EPSILON || rhs === "ε") continue;

      const syms = rhsSymbols(rhs);
      const nullablePositions = syms
        .map((s, i) => (isVariable(s) && nullable.has(s) ? i : -1))
        .filter(i => i >= 0);

      const combinations = 1 << nullablePositions.length;

      for (let mask = 0; mask < combinations; mask++) {
        const remove = new Set<number>();
        nullablePositions.forEach((position, bit) => {
          if (mask & (1 << bit)) {
            remove.add(position);
          }
        });

        const next = syms.filter((_, i) => !remove.has(i));

        // Do NOT add epsilon
        if (!next.length) continue;

        const newRhs = symbolsToRhs(next);
        if (!result.get(lhs)!.has(newRhs)) {
          result.get(lhs)!.add(newRhs);
          if (newRhs !== rhs) {
            generatedAlternatives++;
          }
        }
      }
    }
  }

  // Remove empty variables
  for (const [lhs, set] of [...result]) {
    if (!set.size) {
      result.delete(lhs);
    }
  }

  return {
    grammar: result,
    details: {
      nullable: [...nullable],
      generatedAlternatives,
      preservedStartEpsilon: false
    }
  };
}

/* =========================================================
   STEP 3: UNIT PRODUCTION ELIMINATION
   ========================================================= */

function eliminateUnit(g: Map<string, Set<string>>): StepInfo {
  const result = new Map<string, Set<string>>(
    [...g.keys()].map(k => [k, new Set<string>()])
  );
  const chains: string[] = [];
  let removed = 0;

  for (const source of g.keys()) {
    const closure = new Set<string>([source]);
    const queue = [source];

    while (queue.length) {
      const current = queue.shift()!;
      for (const rhs of g.get(current) || []) {
        const syms = rhsSymbols(rhs);
        if (syms.length === 1 && isVariable(syms[0]) && g.has(syms[0])) {
          if (!closure.has(syms[0])) {
            closure.add(syms[0]);
            queue.push(syms[0]);
          }
          chains.push(`${source} → ${syms[0]}`);
        }
      }
    }

    for (const target of closure) {
      for (const rhs of g.get(target) || []) {
        const syms = rhsSymbols(rhs);
        const isUnit = syms.length === 1 && isVariable(syms[0]) && g.has(syms[0]);

        if (isUnit) {
          removed++;
        } else {
          result.get(source)!.add(rhs);
        }
      }
    }
  }

  for (const [lhs, set] of [...result]) {
    if (!set.size) {
      result.delete(lhs);
    }
  }

  return {
    grammar: result,
    details: {
      unitProductionsRemoved: removed,
      chains: [...new Set(chains)]
    }
  };
}

/* =========================================================
   GRAMMAR SIGNATURE
   ========================================================= */

function grammarSignature(g: Map<string, Set<string>>): string {
  return [...g.entries()]
    .map(([lhs, set]) => `${lhs}->${[...set].sort().join("|")}`)
    .sort()
    .join("\n");
}

/* =========================================================
   FINAL CHECK
   ========================================================= */

function findFinalProblems(g: Map<string, Set<string>>) {
  const uselessResult = eliminateUseless(g);
  const uselessFree =
    grammarSignature(uselessResult.grammar) === grammarSignature(g);

  const epsilonProductions: string[] = [];
  const unitProductions: string[] = [];

  for (const [lhs, set] of g) {
    for (const rhs of set) {
      if (rhs === EPSILON || rhs === "ε") {
        epsilonProductions.push(`${lhs} → ε`);
      }
      const syms = rhsSymbols(rhs);
      if (syms.length === 1 && isVariable(syms[0]) && g.has(syms[0])) {
        unitProductions.push(`${lhs} → ${syms[0]}`);
      }
    }
  }

  return {
    uselessFree,
    epsilonFree: epsilonProductions.length === 0,
    unitFree: unitProductions.length === 0,
    epsilonProductions,
    unitProductions
  };
}

export default function App() {
  const [grammarInput, setGrammarInput] = useState<string>(examples.basic);
  const [editorStatus, setEditorStatus] = useState<string>("Ready");
  const [errorMessage, setErrorMessage] = useState<string | null>(null);
  const [lastRun, setLastRun] = useState<LastRunData | null>(null);
  const [selectedStage, setSelectedStage] = useState<string>("final");
  const [isDark, setIsDark] = useState<boolean>(false);
  const [copyFeedback, setCopyFeedback] = useState<boolean>(false);

  const textareaRef = useRef<HTMLTextAreaElement>(null);
  const lineNumbersRef = useRef<HTMLDivElement>(null);
  const resultsRef = useRef<HTMLElement>(null);
  const inputSectionRef = useRef<HTMLElement>(null);

  // Line numbers calculation
  const lineCount = useMemo(() => {
    return Math.max(1, grammarInput.split("\n").length);
  }, [grammarInput]);

  const activeLinesCount = useMemo(() => {
    return grammarInput.split(/\r?\n/).filter(x => x.trim()).length;
  }, [grammarInput]);

  // Synchronize line numbers scroll with textarea
  const handleScroll = () => {
    if (textareaRef.current && lineNumbersRef.current) {
      lineNumbersRef.current.scrollTop = textareaRef.current.scrollTop;
    }
  };

  // Theme toggle
  const toggleTheme = () => {
    const nextDark = !isDark;
    setIsDark(nextDark);
    if (nextDark) {
      document.documentElement.setAttribute("data-theme", "dark");
    } else {
      document.documentElement.removeAttribute("data-theme");
    }
  };

  // Textarea input changes
  const handleInputChange = (e: React.ChangeEvent<HTMLTextAreaElement>) => {
    const val = e.target.value;
    setGrammarInput(val);
    setErrorMessage(null);

    const lines = val.split(/\r?\n/).filter(x => x.trim());
    const ok = lines.every(x => x.includes("->") || x.includes("→"));
    if (!lines.length) {
      setEditorStatus("Ready");
    } else if (ok) {
      setEditorStatus(`${lines.length} lines detected`);
    } else {
      setEditorStatus("Check syntax");
    }
  };

  // Load example
  const loadExample = (name: string) => {
    const content = examples[name] || examples.basic;
    setGrammarInput(content);
    setErrorMessage(null);
    setEditorStatus("Example loaded");
    if (textareaRef.current) {
      textareaRef.current.focus();
    }
  };

  const handleHeroExample = () => {
    loadExample("complex");
    if (inputSectionRef.current) {
      inputSectionRef.current.scrollIntoView({ behavior: "smooth" });
    }
  };

  const scrollToInput = () => {
    if (inputSectionRef.current) {
      inputSectionRef.current.scrollIntoView({ behavior: "smooth" });
    }
  };

  const handleClear = () => {
    setGrammarInput("");
    setLastRun(null);
    setErrorMessage(null);
    setEditorStatus("Ready");
  };

  // Process CFG
  const processCFG = () => {
    setErrorMessage(null);
    setEditorStatus("Processing…");

    try {
      const raw = parseCFG(grammarInput);

      let current = cloneGrammar(raw);
      const iterations: IterationRecord[] = [];
      let stable = false;
      let pass = 0;
      const MAX_PASSES = 100;

      while (pass < MAX_PASSES) {
        pass++;
        const before = cloneGrammar(current);

        /* ROUND STEP 1 — UNIT */
        const unitInfo = eliminateUnit(current);
        const afterUnit = unitInfo.grammar;

        /* ROUND STEP 2 — USELESS */
        const uselessInfo = eliminateUseless(afterUnit);
        const afterUseless = uselessInfo.grammar;

        /* ROUND STEP 3 — EPSILON */
        const epsilonInfo = eliminateEpsilon(afterUseless);
        const afterEpsilon = epsilonInfo.grammar;

        const changedThisPass =
          grammarSignature(before) !== grammarSignature(afterEpsilon);

        iterations.push({
          pass,
          before,
          unit: afterUnit,
          useless: afterUseless,
          epsilon: afterEpsilon,
          unitInfo,
          uselessInfo,
          epsilonInfo,
          changed: changedThisPass
        });

        current = afterEpsilon;

        if (!changedThisPass) {
          stable = true;
          break;
        }
      }

      // CRITICAL REQUIREMENT: Final answer MUST NOT contain any epsilon sign
      const finalSanitized = removeEpsilonFromGrammar(current);

      const finalProblems = findFinalProblems(finalSanitized);

      if (!stable || !finalProblems.uselessFree || !finalProblems.epsilonFree || !finalProblems.unitFree) {
        throw new Error(
          "The CFG did not reach a completely simplified stable form after repeated Unit → Useless → Epsilon rounds."
        );
      }

      const first = iterations[0];

      const runData: LastRunData = {
        raw,
        unit: first.unit,
        useless: first.useless,
        epsilon: first.epsilon,
        final: finalSanitized,
        unitInfo: {
          grammar: finalSanitized,
          details: {
            unitProductionsRemoved: iterations.reduce(
              (total, item) => total + (item.unitInfo.details.unitProductionsRemoved || 0),
              0
            ),
            chains: [
              ...new Set(iterations.flatMap(item => item.unitInfo.details.chains || []))
            ],
            passes: pass,
            stable: true,
            finalProblems
          }
        },
        uselessInfo: first.uselessInfo,
        epsilonInfo: first.epsilonInfo,
        iterations
      };

      setLastRun(runData);
      setSelectedStage("final");
      setEditorStatus(`Processed ✓ (${pass} round${pass === 1 ? "" : "s"})`);

      setTimeout(() => {
        if (resultsRef.current) {
          resultsRef.current.scrollIntoView({ behavior: "smooth", block: "start" });
        }
      }, 50);

    } catch (err: any) {
      setLastRun(null);
      setErrorMessage(err.message || "The grammar could not be processed.");
      setEditorStatus("Needs attention");
    }
  };

  // Copy final CFG without epsilon
  const copyFinal = () => {
    if (!lastRun) return;
    const finalClean = removeEpsilonFromGrammar(lastRun.final);
    const text = formatGrammar(finalClean);
    navigator.clipboard.writeText(text).then(
      () => {
        setCopyFeedback(true);
        setTimeout(() => setCopyFeedback(false), 1200);
      },
      () => {
        setErrorMessage("Clipboard access was blocked. Please select and copy manually.");
      }
    );
  };

  // Download final CFG
  const downloadFinal = () => {
    if (!lastRun) return;

    const iterationText = lastRun.iterations
      .map(
        item =>
          `Pass ${item.pass}: ${
            item.changed
              ? "Grammar changed → checked again"
              : "No change → FINAL ANSWER"
          }`
      )
      .join("\n");

    const finalClean = removeEpsilonFromGrammar(lastRun.final);

    const text = `CFG Pipeline Simplifier

========================================
ORIGINAL CFG
========================================

${formatGrammar(lastRun.raw)}


========================================
STEP 1 — USELESS SYMBOL ELIMINATION
========================================

${formatGrammar(lastRun.useless)}


========================================
STEP 2 — EPSILON PRODUCTION ELIMINATION
========================================

${formatGrammar(lastRun.epsilon)}


========================================
FINAL ANSWER — STABLE SIMPLIFIED CFG
(Guaranteed No Epsilon)
========================================

${formatGrammar(finalClean)}


========================================
ITERATION CHECK
========================================

${iterationText}


========================================
FINAL VERIFICATION
========================================

No epsilon productions
No unit productions
No useless symbols

The complete pipeline was repeated
until no further change occurred.
`;

    const blob = new Blob([text], { type: "text/plain" });
    const a = document.createElement("a");
    a.href = URL.createObjectURL(blob);
    a.download = "cfg-simplification-result.txt";
    a.click();
    URL.revokeObjectURL(a.href);
  };

  // Stage Panel data calculation
  const stageData = useMemo(() => {
    if (!lastRun) return null;

    if (selectedStage === "raw") {
      return {
        title: "Original CFG",
        subtitle: "Parsed grammar before simplification",
        grammar: lastRun.raw,
        info: null
      };
    }

    if (selectedStage === "unit") {
      return {
        title: "Step 1 — Unit Production Elimination",
        subtitle: "Round 1: remove variable-to-variable chains using unit closure",
        grammar: lastRun.unit,
        info: lastRun.iterations[0].unitInfo.details
      };
    }

    if (selectedStage === "useless") {
      return {
        title: "Step 2 — Useless Symbol Elimination",
        subtitle: "Round 1: remove non-generating and unreachable symbols",
        grammar: lastRun.useless,
        info: lastRun.iterations[0].uselessInfo.details
      };
    }

    if (selectedStage === "epsilon") {
      return {
        title: "Step 3 — Epsilon Production Elimination",
        subtitle: "Round 1: remove ε and generate equivalent alternatives",
        grammar: lastRun.epsilon,
        info: lastRun.iterations[0].epsilonInfo.details
      };
    }

    // Default "final"
    // Ensured: NO EPSILON SIGN IN FINAL ANSWER
    const finalClean = removeEpsilonFromGrammar(lastRun.final);
    return {
      title: "FINAL ANSWER — Stable Simplified CFG",
      subtitle: `Complete pipeline checked ${lastRun.unitInfo.details.passes} time${
        lastRun.unitInfo.details.passes === 1 ? "" : "s"
      } until no further change occurred.`,
      grammar: finalClean,
      info: lastRun.unitInfo.details
    };
  }, [lastRun, selectedStage]);

  return (
    <div className="app-shell">
      {/* Top Header */}
      <header className="topbar">
        <div className="brand">
          <div className="brand-mark">CFG</div>
          <div>
            <h1>CFG Pipeline Simplifier</h1>
            <p>Interactive Formal Languages Laboratory</p>
          </div>
        </div>
        <div className="top-actions">
          <span className="mode-badge">
            <span className="pulse"></span> Client-side • No Backend
          </span>
          <button
            id="themeBtn"
            className="icon-btn"
            title="Toggle theme"
            aria-label="Toggle theme"
            onClick={toggleTheme}
          >
            {isDark ? "☀" : "☾"}
          </button>
        </div>
      </header>

      <main className="container">
        {/* Hero Section */}
        <section className="hero">
          <div className="hero-content">
            <span className="eyebrow">FORMAL LANGUAGES &amp; AUTOMATA</span>
            <h2>
              Turn a raw CFG into a<br />
              <span>cleaner grammar.</span>
            </h2>
            <p>
              Explore the complete three-step simplification pipeline with live statistics,
              algorithm traces, and stage-by-stage results.
            </p>
            <div className="hero-actions">
              <button
                id="heroExampleBtn"
                className="btn btn-primary"
                onClick={handleHeroExample}
              >
                Try Interactive Example <span>→</span>
              </button>
              <button
                id="scrollInputBtn"
                className="btn btn-light"
                onClick={scrollToInput}
              >
                Enter Your CFG
              </button>
            </div>
          </div>
          <div className="hero-visual" aria-hidden="true">
            <div className="diagram-ring ring-1"></div>
            <div className="diagram-ring ring-2"></div>
            <div className="diagram-center">G</div>
            <div className="diagram-chip chip-1">S → AB</div>
            <div className="diagram-chip chip-2">A → ε</div>
            <div className="diagram-chip chip-3">B → C</div>
            <div className="diagram-chip chip-4">✓</div>
          </div>
        </section>

        {/* Workspace: Input & Guide */}
        <section id="inputSection" ref={inputSectionRef} className="workspace-grid">
          <div className="card editor-card">
            <div className="card-header">
              <div>
                <span className="eyebrow">01 / INPUT</span>
                <h2>Define your grammar</h2>
              </div>
              <span id="editorStatus" className="editor-status">
                {editorStatus}
              </span>
            </div>

            <div className="format-bar">
              <span><b>Syntax</b> A → B | a</span>
              <span><b>Epsilon</b> ε / epsilon / e</span>
              <span><b>Start</b> first variable</span>
            </div>

            <div className="editor-wrap">
              <div
                className="line-numbers"
                id="lineNumbers"
                ref={lineNumbersRef}
              >
                {Array.from({ length: lineCount }, (_, i) => i + 1).join("\n")}
              </div>
              <textarea
                id="grammarInput"
                ref={textareaRef}
                spellCheck="false"
                aria-label="CFG input"
                placeholder={`S -> AB | a\nA -> a | ε\nB -> b | A\nC -> c\nD -> E\nE -> D`}
                value={grammarInput}
                onChange={handleInputChange}
                onScroll={handleScroll}
              />
            </div>

            {errorMessage && (
              <div id="errorBox" className="error-box">
                {errorMessage}
              </div>
            )}

            <div className="editor-footer">
              <div className="button-row">
                <button
                  id="processBtn"
                  className="btn btn-primary"
                  onClick={processCFG}
                >
                  ▶ Process CFG
                </button>
                <button
                  id="exampleBtn"
                  className="btn btn-light"
                  onClick={() => loadExample("basic")}
                >
                  Load Example
                </button>
                <button
                  id="clearBtn"
                  className="btn btn-ghost"
                  onClick={handleClear}
                >
                  Clear
                </button>
              </div>
              <span id="inputCount" className="muted">
                {activeLinesCount} line(s)
              </span>
            </div>
          </div>

          <aside className="card guide-card">
            <div className="card-header">
              <div>
                <span className="eyebrow">QUICK GUIDE</span>
                <h2>Pipeline</h2>
              </div>
            </div>
            <div className="mini-pipeline">
              <div className="mini-step active">
                <span>01</span>
                <div>
                  <b>Unit</b>
                  <small>Remove A → B chains</small>
                </div>
              </div>
              <div className="mini-connector"></div>
              <div className="mini-step">
                <span>02</span>
                <div>
                  <b>Useless</b>
                  <small>Generating + reachable</small>
                </div>
              </div>
              <div className="mini-connector"></div>
              <div className="mini-step">
                <span>03</span>
                <div>
                  <b>Epsilon</b>
                  <small>Nullable variables</small>
                </div>
              </div>
              <div className="mini-connector"></div>
              <div className="mini-step final">
                <span>✓</span>
                <div>
                  <b>Final CFG</b>
                  <small>Simplified result (No ε)</small>
                </div>
              </div>
            </div>
            <div className="tip-box">
              <span>💡</span>
              <div>
                <b>Good to know</b>
                <p>Each transformation uses the previous stage as its input. Nothing is hardcoded.</p>
              </div>
            </div>
          </aside>
        </section>

        {/* Examples Strip */}
        <section className="examples-strip">
          <div>
            <span className="eyebrow">PRACTICE LAB</span>
            <h2>Test different CFG patterns</h2>
          </div>
          <div className="example-pills">
            <button data-example="basic" onClick={() => loadExample("basic")}>Basic</button>
            <button data-example="epsilon" onClick={() => loadExample("epsilon")}>Epsilon</button>
            <button data-example="unit" onClick={() => loadExample("unit")}>Unit Chain</button>
            <button data-example="useless" onClick={() => loadExample("useless")}>Useless Symbols</button>
            <button data-example="complex" onClick={() => loadExample("complex")}>Complex</button>
          </div>
        </section>

        {/* Results Section */}
        {lastRun && (
          <section id="resultsSection" ref={resultsRef} className="results">
            <div className="results-top">
              <div>
                <span className="eyebrow">02 / ANALYSIS</span>
                <h2>Pipeline results</h2>
                <p id="resultSummary">
                  {`${lastRun.raw.size} variables entered → ${lastRun.final.size} variables remain after ${
                    lastRun.unitInfo.details.passes
                  } complete round${lastRun.unitInfo.details.passes === 1 ? "" : "s"}. `}
                  {`Each round: Unit → Useless → Epsilon. Final verification: no ε, no unit productions, no useless symbols.`}
                </p>
              </div>
              <div className="result-actions">
                <button
                  id="copyBtn"
                  className="btn btn-light"
                  onClick={copyFinal}
                >
                  {copyFeedback ? "✓ Copied" : "Copy Final CFG"}
                </button>
                <button
                  id="downloadBtn"
                  className="btn btn-light"
                  onClick={downloadFinal}
                >
                  Download .txt
                </button>
              </div>
            </div>

            {/* Metrics */}
            <div className="metric-grid">
              <div className="metric">
                <span>Original</span>
                <strong id="metricOriginal">{countProductions(lastRun.raw)}</strong>
                <small>productions</small>
              </div>
              <div className="metric">
                <span>Useless removed</span>
                <strong id="metricRemoved">
                  {Math.max(0, countProductions(lastRun.raw) - countProductions(lastRun.final))}
                </strong>
                <small>symbols / rules</small>
              </div>
              <div className="metric">
                <span>Nullable</span>
                <strong id="metricNullable">
                  {lastRun.epsilonInfo.details.nullable?.length || 0}
                </strong>
                <small>variables</small>
              </div>
              <div className="metric success">
                <span>Final</span>
                <strong id="metricFinal">{countProductions(lastRun.final)}</strong>
                <small>productions</small>
              </div>
            </div>

            {/* Stage Tabs */}
            <div className="stage-tabs">
              <button
                className={`stage-tab ${selectedStage === "raw" ? "active" : ""}`}
                data-stage="raw"
                onClick={() => setSelectedStage("raw")}
              >
                Original
              </button>
              <button
                className={`stage-tab ${selectedStage === "unit" ? "active" : ""}`}
                data-stage="unit"
                onClick={() => setSelectedStage("unit")}
              >
                01 Unit
              </button>
              <button
                className={`stage-tab ${selectedStage === "useless" ? "active" : ""}`}
                data-stage="useless"
                onClick={() => setSelectedStage("useless")}
              >
                02 Useless
              </button>
              <button
                className={`stage-tab ${selectedStage === "epsilon" ? "active" : ""}`}
                data-stage="epsilon"
                onClick={() => setSelectedStage("epsilon")}
              >
                03 Epsilon
              </button>
              <button
                className={`stage-tab ${selectedStage === "final" ? "active" : ""}`}
                data-stage="final"
                onClick={() => setSelectedStage("final")}
              >
                Final Answer
              </button>
            </div>

            {/* Stage Panel */}
            {stageData && (
              <div id="stagePanel" className="stage-panel">
                <div className="stage-head">
                  <div>
                    <h3>{stageData.title}</h3>
                    <p>{stageData.subtitle}</p>
                  </div>
                  <div className="stats">
                    <span className="stat">Variables: {stageData.grammar.size}</span>
                    <span className="stat">Productions: {countProductions(stageData.grammar)}</span>
                  </div>
                </div>

                {/* Formatted Grammar Box: guaranteed no epsilon sign in final stage */}
                <pre className="grammar-box">
                  {formatGrammar(stageData.grammar)}
                </pre>

                {/* Stage Details Trace */}
                {selectedStage === "useless" && stageData.info && (
                  <div className="stage-detail">
                    <b>Algorithm trace</b>
                    <ul>
                      <li>Generating variables: {stageData.info.generating?.join(", ") || "None"}</li>
                      <li>Removed non-generating: {stageData.info.nonGenerating?.join(", ") || "None"}</li>
                      <li>Reachable variables: {stageData.info.reachable?.join(", ") || "None"}</li>
                      <li>Removed unreachable: {stageData.info.unreachable?.join(", ") || "None"}</li>
                    </ul>
                  </div>
                )}

                {selectedStage === "epsilon" && stageData.info && (
                  <div className="stage-detail">
                    <b>Algorithm trace</b>
                    <ul>
                      <li>Nullable variables: {stageData.info.nullable?.join(", ") || "None"}</li>
                      <li>Equivalent alternatives generated: {stageData.info.generatedAlternatives || 0}</li>
                      <li>ε productions remaining after this step: 0</li>
                    </ul>
                  </div>
                )}

                {selectedStage === "unit" && stageData.info && (
                  <div className="stage-detail">
                    <b>Algorithm trace</b>
                    <ul>
                      <li>Unit-production links removed: {stageData.info.unitProductionsRemoved || 0}</li>
                      <li>
                        Closure links:{" "}
                        {stageData.info.chains?.slice(0, 10).join(", ") || "None"}
                      </li>
                    </ul>
                  </div>
                )}

                {selectedStage === "final" && stageData.info && (
                  <>
                    <div className="stage-detail">
                      <b>Algorithm trace</b>
                      <ul>
                        <li>Complete rounds: {stageData.info.passes || 1}</li>
                        <li>
                          Final check — Useless symbols:{" "}
                          {stageData.info.finalProblems?.uselessFree ? "None ✓" : "Found"}
                        </li>
                        <li>
                          Final check — Epsilon productions:{" "}
                          {stageData.info.finalProblems?.epsilonFree ? "None ✓" : "Found"}
                        </li>
                        <li>
                          Final check — Unit productions:{" "}
                          {stageData.info.finalProblems?.unitFree ? "None ✓" : "Found"}
                        </li>
                      </ul>
                    </div>

                    <div className="stage-detail">
                      <b>Iteration Check</b>
                      <ul>
                        {lastRun.iterations.map(item => (
                          <li key={item.pass}>
                            <b>Pass {item.pass}</b>:{" "}
                            {item.changed
                              ? "Grammar changed → CHECK AGAIN"
                              : "No change → FINAL ANSWER ✓"}
                          </li>
                        ))}
                      </ul>
                    </div>

                    <div className="success-banner">
                      ✓ FINAL ANSWER
                      <br /><br />
                      Useless symbols: None ✓
                      <br />
                      Epsilon productions: None ✓
                      <br />
                      Unit productions: None ✓
                      <br /><br />
                      The complete Unit → Useless → Epsilon pipeline was repeated until
                      no further change was detected.
                    </div>
                  </>
                )}

                {selectedStage === "raw" && (
                  <div className="stage-detail">
                    <b>Algorithm trace</b>
                    <ul>
                      <li>This is the parsed input grammar. The first variable is used as the start symbol.</li>
                    </ul>
                  </div>
                )}
              </div>
            )}

            {/* Pipeline Flow Row */}
            <div className="flow-row">
              <div className="flow-card">
                <span>01</span>
                <b>Unit</b>
                <small>Remove variable-to-variable productions using unit closure.</small>
              </div>
              <div className="flow-arrow">→</div>
              <div className="flow-card">
                <span>02</span>
                <b>Useless</b>
                <small>Remove non-generating and unreachable symbols.</small>
              </div>
              <div className="flow-arrow">→</div>
              <div className="flow-card">
                <span>03</span>
                <b>Epsilon</b>
                <small>Remove ε and generate equivalent alternatives.</small>
              </div>
            </div>
          </section>
        )}

        {/* Viva Mode Educational Section */}
        <section className="learn-section">
          <div className="section-heading">
            <span className="eyebrow">VIVA MODE</span>
            <h2>Understand what the algorithm is doing</h2>
            <p>Use these checkpoints when explaining the project during a practical examination.</p>
          </div>
          <div className="learn-grid">
            <article className="learn-card">
              <div className="learn-number">01</div>
              <h3>Generating</h3>
              <p>
                Start with variables that directly produce terminals, then repeatedly add variables
                whose right-hand sides are already known to generate terminal strings.
              </p>
            </article>
            <article className="learn-card">
              <div className="learn-number">02</div>
              <h3>Nullable</h3>
              <p>
                A variable is nullable when it can derive ε. The algorithm finds nullable variables
                to a fixed point before creating alternatives.
              </p>
            </article>
            <article className="learn-card">
              <div className="learn-number">03</div>
              <h3>Unit Closure</h3>
              <p>
                For A → B, B → C, the closure connects A with C so non-unit productions can be transferred
                back to A.
              </p>
            </article>
          </div>
        </section>

        {/* Accepted Grammar Format */}
        <section className="card notation-card">
          <div>
            <span className="eyebrow">NOTATION</span>
            <h2>Accepted grammar format</h2>
          </div>
          <div className="notation-grid">
            <div>
              <code>S -&gt; AB | a</code>
              <span>Alternatives with |</span>
            </div>
            <div>
              <code>A -&gt; ε</code>
              <span>Epsilon production</span>
            </div>
            <div>
              <code>B -&gt; C</code>
              <span>Unit production</span>
            </div>
            <div>
              <code>A -&gt; aA</code>
              <span>Mixed terminal + variable</span>
            </div>
          </div>
        </section>
      </main>

      {/* Footer */}
      <footer>
        <div className="container footer-inner">
          <span>CFG Pipeline Simplifier</span>
          <span>Formal Languages &amp; Automata • Interactive Laboratory</span>
        </div>
      </footer>
    </div>
  );
}
