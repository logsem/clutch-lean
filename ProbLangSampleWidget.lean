module

public meta import Metrology.ProbLang.Interp.Sample
public meta import Lean.Elab.Eval
public meta import Lean.Server.Rpc.RequestHandling
public meta import Lean.Util.Path
public meta import Lean.Widget.UserWidget

public meta section

/-! # `#sample`

`#sample e` shows a widget that runs the program `e : Exp Float` many times and plots what it
returns: how often it returned `true`, `false`, an integer, a real or anything else, and
histograms of the integers and the finite reals. Nothing runs until *Play* is pressed. The charts
fill in as results come back; *Pause* stops, and *Play* then resumes.

```
#sample pl(urand)
#sample pl(urand) with Real := fun x => if 0 ≤ x && x ≤ 1 then 1 else 0
```

Options go after `with`, one per line or separated by commas:

* `title := s` titles the widget (default `"Samples"`);
* `engine := s` picks the engine it starts with (default the first of `engines`, `"tacoma"`);
* `runs := n` is the number of runs it starts with (default `10000`);
* `bins := n` is the number of bins of the real histogram it starts with (default `30`);
* `boolFun := f`, `intFun := f` and `realFun := f` (of types `Bool → Float`, `Int → Float` and
  `Float → Float`) give curves to draw over the matching charts: probabilities for `Bool` and
  `Int`, a density for reals.

The widget's controls can still change the engine, runs and bins.

```
#sample pl% urand + urand
  with
    title := "Sum of two uniforms"
    bins := 50
    realFun := fun x => max 0 (1 - (x - 1).abs)
```

The widget is attached to an info message, so the infoview's *All Messages* shows every `#sample`
of a file at once. A widget keeps its charts and controls while it is off screen, and pauses if
it was running; `set_option sample.maxSaved n` bounds how many widgets are kept (default 16).
Widgets keep their state across edits and reloads of the file, unless the file starts with
`#sample_session`: then reloading it, or editing that command, starts every widget afresh.
`#sample_session with maxSaved := n` also sets `sample.maxSaved` for the rest of the file.

The runs happen in the `problang-sample` executable, which Lake builds before this module. Each
Play starts one, which streams results back until it is done or paused. In a `module` file, the
modules that define the program and curves must be `meta import`ed, as for any code run at
elaboration time.
-/

open Lean Server Elab

namespace ProbLang.Interp.Sample

/-- A `#sample` command, kept on the server for the widget to run. -/
structure Job where
  program : Exp Float
  boolCurve? : Option (Bool → Float) := none
  intCurve? : Option (Int → Float) := none
  realCurve? : Option (Float → Float) := none
  deriving TypeName

/-- How often `problang-sample` reports, in milliseconds. -/
def updateMillis : Nat := 100

/-- A `Real` curve is drawn through this many points. -/
def curvePoints : Nat := 256

/-- An `Int` curve is drawn only across at most this many integers. -/
def maxIntCurve : Nat := 100000

/-- Where `lake build` puts `problang-sample`: in `bin/`, beside the `lib/lean/` that holds
`Metrology`. -/
def samplerPath : IO System.FilePath := do
  let olean ← findOLean `Metrology
  let some lib := olean.parent | throw (.userError s!"no directory in {olean}")
  return (lib / ".." / ".." / "bin" / "problang-sample").addExtension System.FilePath.exeExtension

/-- A running `problang-sample`, kept on the server for the widget to read from. -/
structure Run where
  child : IO.Process.Child { stdin := .piped, stdout := .piped, stderr := .piped }
  /-- Whether the process has been waited for, after which its pid may be reused. -/
  reaped : IO.Ref Bool
  /-- Whether a `nextChunk` is reading from it. -/
  reading : IO.Ref Bool
  deriving TypeName

/-- Kill the process, unless it has already been waited for. -/
def Run.stop (run : Run) : IO Unit := do
  unless ← run.reaped.swap true do
    run.child.kill
    discard run.child.wait

/-- The parameters of `startSample`. -/
structure StartParams where
  job : WithRpcRef Job
  engine : String
  runs : Nat
  deriving RpcEncodable

/-- Start running a `#sample` job `runs` times. -/
@[server_rpc_method]
def startSample (p : StartParams) : RequestM (RequestTask (WithRpcRef Run)) := RequestM.asTask do
  unless 0 < p.runs do
    throw (.invalidParams "the number of runs must be positive")
  unless engines.any (·.1 == p.engine) do
    throw (.invalidParams s!"unknown engine: {p.engine}")
  let exe ← samplerPath
  unless ← exe.pathExists do
    throw (.internalError s!"{exe} does not exist; run `lake build problang-sample`")
  let child ← IO.Process.spawn {
    cmd := exe.toString, args := #[p.engine, toString p.runs, toString updateMillis]
    stdin := .piped, stdout := .piped, stderr := .piped }
  -- `child` holds stdin open until the `Run` is dropped, as `problang-sample` expects.
  child.stdin.putStrLn (encodeProgram p.job.val.program)
  child.stdin.flush
  let run : Run := { child, reaped := ← IO.mkRef false, reading := ← IO.mkRef false }
  if ← (← read).cancelTk.wasCancelledByCancelRequest then
    run.stop
    throw .requestCancelled
  WithRpcRef.mk run

/-- The parameters of `nextChunk` and `stopSample`. -/
structure RunParams where
  run : WithRpcRef Run
  deriving RpcEncodable

/-- The next `Summary` a run reports, floats as hex bits, or `null` once it has ended. Cancelling
the request stops the run. -/
@[server_rpc_method]
def nextChunk (p : RunParams) : RequestM (RequestTask Json) := RequestM.asTask do
  let run := p.run.val
  if ← run.reading.swap true then
    throw (.invalidParams "this run is already being read")
  try
    let line ← ServerTask.IO.asTask run.child.stdout.getLine
    -- An edit also marks the request cancelled, but still delivers its result, so ignore it.
    let cancelled := (← read).cancelTk.requestCancellationTask.mapCheap fun _ => none
    let some line ← ServerTask.waitAny [line.mapCheap some, cancelled]
      | run.stop; throw .requestCancelled
    let line ← IO.ofExcept line
    if !line.isEmpty then
      match Json.parse line with
      | .ok summary => return summary
      | .error err => throw (.internalError s!"cannot read the output of problang-sample: {err}")
    -- The output has ended: the process has exited, or was stopped.
    unless ← run.reaped.swap true do
      unless (← run.child.wait) == 0 do
        let err ← run.child.stderr.readToEnd
        throw (.internalError s!"problang-sample failed: {err.trimAscii}")
    return .null
  finally
    run.reading.set false

/-- Stop a run. -/
@[server_rpc_method]
def stopSample (p : RunParams) : RequestM (RequestTask Unit) := RequestM.asTask p.run.val.stop

/-- The parameters of `sampleCurves`: the ranges the histograms span. -/
structure CurveParams where
  job : WithRpcRef Job
  intRange? : Option (Int × Int) := none
  realRange? : Option (Float × Float) := none
  deriving RpcEncodable

/-- A job's curves, at the points where the widget draws them. -/
structure Curves (R : Type) where
  /-- The `Bool` curve at `true` and `false`. -/
  bool? : Option (R × R) := none
  /-- The `Int` curve at each integer of the range. -/
  int? : Option (Array R) := none
  /-- The `Real` curve at `curvePoints` evenly spaced points across the range. -/
  real? : Option (Array R) := none
  /-- Why a curve is missing. -/
  notes : Array String := #[]
  deriving ToJson

/-- Evaluate a `#sample` job's curves over the given ranges, floats as hex bits. -/
@[server_rpc_method]
def sampleCurves (p : CurveParams) : RequestM (RequestTask Json) := RequestM.asTask do
  let job := p.job.val
  let mut c : Curves Float := { bool? := job.boolCurve?.map fun f => (f true, f false) }
  if let (some f, some (lo, hi)) := (job.intCurve?, p.intRange?) then
    if hi - lo < maxIntCurve then
      let x (i : Nat) : Int := lo + i
      c := { c with int? := some <| (Array.range (hi - lo + 1).toNat).map (f ∘ x) }
    else
      let note := s!"The Int curve is not drawn: the results span more than {maxIntCurve} integers."
      c := { c with notes := c.notes.push note }
  if let (some f, some (lo, hi)) := (job.realCurve?, p.realRange?) then
    let x (i : Nat) := lo + (hi - lo) * i.toFloat / (curvePoints - 1).toFloat
    c := { c with real? := some <| (Array.range curvePoints).map (f ∘ x) }
  return letI := hexToJson; toJson c

/-- The `#sample` widget. -/
@[widget_module]
def sampleWidget : Widget.Module where
  javascript := r#"
import * as React from 'react'
import { mapRpcError, useRpcSession } from '@leanprover/infoview'

const h = React.createElement

// Floats arrive as the 16 hex digits of their IEEE bits, from position `i` of `hex`; see
// `Sample.lean`.
const bits = new DataView(new ArrayBuffer(8))
function float(hex, i = 0) {
  bits.setUint32(0, parseInt(hex.slice(i, i + 8), 16))
  bits.setUint32(4, parseInt(hex.slice(i + 8, i + 16), 16))
  return bits.getFloat64(0)
}
const floats = xs => xs && xs.map(x => float(x))
// The reals of a summary, packed into one string.
const unpack = hex => Array.from({ length: hex.length / 16 }, (_, i) => float(hex, 16 * i))

// The runs so far, as a `Summary` with its floats decoded.
const noRuns = { runs: 0, bools: [0, 0], ints: [], reals: [], other: 0 }

// Add the chunk `c`, as it arrived, to `s`.
function merge(s, c) {
  const ints = new Map(s.ints)
  for (const [v, n] of c.ints) ints.set(v, (ints.get(v) ?? 0) + n)
  return {
    runs: s.runs + c.runs,
    bools: [s.bools[0] + c.bools[0], s.bools[1] + c.bools[1]],
    ints: [...ints].sort((a, b) => a[0] - b[0]),
    reals: s.reals.concat(unpack(c.reals)),
    other: s.other + c.other,
    failure: s.failure ?? c.failure,
  }
}

// Charts are drawn on a grid of N × N square cells.
const N = 10

// The least `[a, a + N s]` that contains `[lo, hi]` about its middle, where the step `s` is 1, 2
// or 5 times a power of ten, and at least `min`, and `a` is a multiple of `s`: so the grid lines
// fall on round numbers. `undefined` if there is none among the floats.
function niceDomain(lo, hi, min = 0) {
  let e = Math.floor(Math.log10(Math.max((hi - lo) / N, min) || Math.abs(lo) / N || 1 / N))
  for (;;) {
    for (const m of [1, 2, 5]) {
      const s = Math.max(min, m * 10 ** e)
      // The multiples of `s` from which N steps cover `[lo, hi]`; take the most central.
      const first = Math.ceil(hi / s - N) * s, last = Math.floor(lo / s) * s
      if (!Number.isFinite(first) || !Number.isFinite(last + N * s)) return undefined
      if (first <= last) {
        const a = Math.min(last, Math.max(first, Math.round((lo + hi) / 2 / s - N / 2) * s))
        return [a, a + N * s]
      }
    }
    e++
  }
}

// The domains of the `Int` and `Real` histograms; `undefined` for one with no results, or that
// cannot be drawn.
function domains(s) {
  const int = s.ints.length > 0 ?
    niceDomain(s.ints[0][0], s.ints[s.ints.length - 1][0] + 1, 1) : undefined
  let lo = Infinity, hi = -Infinity
  for (const x of s.reals) { lo = Math.min(lo, x); hi = Math.max(hi, x) }
  return { int, real: s.reals.length > 0 ? niceDomain(lo, hi) : undefined }
}

const fmt = x => String(Number(x.toPrecision(4)))
// A probability as a percentage, short enough to fit in a bar.
const percent = p => p === 0 ? '0%' : p < 0.001 ? '<0.1%' :
  p < 0.1 ? `${(100 * p).toFixed(1)}%` : `${Math.round(100 * p)}%`
const runsOf = (count, runs) => `${count} of ${runs} run${runs === 1 ? '' : 's'}`

// A bar is `{ x0, x1, y, curve, hint, value }` in data coordinates, where `curve` is the curve's
// value for the bar and `value` a label to show above it, if any.

function outcomeBars(s, curve) {
  const ints = s.ints.reduce((sum, [, n]) => sum + n, 0)
  return [['True', s.bools[0], curve?.[0]], ['False', s.bools[1], curve?.[1]],
          ['Int', ints], ['Real', s.reals.length], ['Other', s.other]]
    .map(([label, count, c], i) => ({
      x0: 2 * i + 0.2, x1: 2 * i + 1.8, y: count / s.runs, curve: c,
      value: percent(count / s.runs),
      hint: `P[${label}] = ${fmt(count / s.runs)}: ${runsOf(count, s.runs)}`,
    }))
}

// `curve` holds the curve's values at the integers from `a` up to `b`.
function intBars(s, [a, b], curve) {
  // Up to five bars per grid cell.
  const w = Math.max(1, (b - a) / N / 5)
  const bars = Array.from({ length: Math.round((b - a) / w) }, (_, i) => {
    const lo = a + i * w, hi = lo + w - 1
    return { x0: lo, x1: lo + w, count: 0, label: w === 1 ? `${lo}` : `${lo}–${hi}`,
             curve: curve?.slice(i * w, (i + 1) * w).reduce((sum, y) => sum + y, 0) }
  })
  for (const [v, n] of s.ints)
    bars[Math.max(0, Math.min(bars.length - 1, Math.floor((v - a) / w)))].count += n
  for (const bar of bars) {
    bar.y = bar.count / s.runs
    bar.hint = `${bar.label}: ${runsOf(bar.count, s.runs)}`
  }
  return bars
}

function realBars(s, bins, [a, b]) {
  const edge = i => i === bins ? b : a + (b - a) * i / bins
  const bars = Array.from({ length: bins }, (_, i) => ({ x0: edge(i), x1: edge(i + 1), count: 0 }))
  for (const x of s.reals)
    bars[Math.max(0, Math.min(bins - 1, Math.floor((x - a) / (b - a) * bins)))].count++
  for (const bar of bars) {
    bar.y = bar.count / s.runs / (bar.x1 - bar.x0)
    bar.hint = `[${fmt(bar.x0)}, ${fmt(bar.x1)}]: ${runsOf(bar.count, s.runs)}`
  }
  return bars
}

// The top of a chart of `bars` and `line`: a quarter above the highest point, rounded up to two
// significant digits, so that it moves in small steps.
function top(bars, line = []) {
  let y = 0
  for (const v of [...bars.flatMap(b => [b.y, b.curve]), ...line.map(p => p[1])])
    if (Number.isFinite(v) && v > y) y = v
  y *= 1.25
  if (!(y > 0 && Number.isFinite(y))) return 1
  const unit = 10 ** (Math.floor(Math.log10(y)) - 1)
  return Math.ceil(y / unit) * unit
}

const fg = 'var(--vscode-editor-foreground)', bg = 'var(--vscode-editor-background)'
// The chart's size, and its plot area: `P × P` at (`LEFT`, `TOP`).
const S = 200, LEFT = 30, TOP = 8, P = 160

// A chart over `[x0, x1] × [0, y1]`, on the grid. `line` is a curve drawn through points, `ticks`
// label the x axis, and `message` lines are shown in the middle.
function Chart({ x0, x1, y1, bars = [], line, ticks, message = [] }) {
  const sx = x => LEFT + (x - x0) / (x1 - x0) * P
  const sy = y => TOP + P - y / y1 * P
  const text = (key, x, y, anchor, s, props) =>
    h('text', { key, x, y, textAnchor: anchor, fontSize: 9, fill: fg, ...props }, s)
  const grid = { stroke: fg, strokeOpacity: 0.15, strokeWidth: 0.5 }
  return h('svg', { viewBox: `0 0 ${S} ${S}`, style: { display: 'block', width: '100%' } },
    Array.from({ length: N + 1 }, (_, i) => h(React.Fragment, { key: i },
      h('line', { x1: LEFT + i * P / N, x2: LEFT + i * P / N, y1: TOP, y2: TOP + P, ...grid }),
      h('line', { x1: LEFT, x2: LEFT + P, y1: TOP + i * P / N, y2: TOP + i * P / N, ...grid }))),
    bars.map((b, i) => b.y > 0 && (() => {
      const w = sx(b.x1) - sx(b.x0)
      return h('rect', {
        key: i, x: sx(b.x0), width: w > 2 ? w - 0.5 : w, y: sy(b.y), height: sy(0) - sy(b.y),
        fill: fg },
        h('title', null, b.curve === undefined ? b.hint : `${b.hint}; curve ${fmt(b.curve)}`))
    })()),
    // A bar's value goes inside its top, or above it if the bar is too short.
    bars.filter(b => b.value).map((b, i) => {
      const inside = sy(0) - sy(b.y) >= 12
      return text(`v${i}`, sx((b.x0 + b.x1) / 2), inside ? sy(b.y) + 9 : sy(b.y) - 3, 'middle',
                  b.value, { fontSize: 8, fill: inside ? bg : fg })
    }),
    // A curve's value of 0 would only mark the axis.
    bars.filter(b => Number.isFinite(b.curve) && b.curve !== 0).map((b, i) => h('circle', {
      key: `c${i}`, cx: sx((b.x0 + b.x1) / 2), cy: sy(b.curve), r: 2,
      fill: fg, stroke: bg, strokeWidth: 0.75 })),
    line && h('polyline', {
      fill: 'none', stroke: fg, strokeWidth: 0.5, strokeLinejoin: 'round',
      points: line.filter(([, y]) => Number.isFinite(y)).map(([x, y]) => `${sx(x)},${sy(y)}`)
        .join(' ') }),
    text('top', LEFT - 3, TOP + 3, 'end', fmt(y1)),
    text('zero', LEFT - 3, TOP + P + 3, 'end', '0'),
    ticks.map(([x, s], i) => text(`t${i}`, sx(x), TOP + P + 12, 'middle', s)),
    message.map((s, i) =>
      text(`m${i}`, LEFT + P / 2, TOP + P / 2 + 12 * (i - (message.length - 1) / 2), 'middle', s)))
}

const oneLine = { whiteSpace: 'nowrap', overflow: 'hidden', textOverflow: 'ellipsis' }

// A square with a one-line title and footer, so that its size never depends on its contents.
function Square({ title, footer, children }) {
  return h('div', { style: { minWidth: 0 } },
    h('div', { style: { ...oneLine, textAlign: 'center' } }, title),
    children,
    h('div', { style: { ...oneLine, height: '2.4em', lineHeight: '2.4em' },
               title: typeof footer === 'string' ? footer : undefined }, footer))
}

const maxSlider = 100

function Charts({ data, bins, binsText, editBins }) {
  const s = data?.summary ?? noRuns, d = data?.domains ?? {}, c = data?.curves
  const ran = s.runs > 0
  const outcomes = ran ?
    h(Chart, { x0: 0, x1: 10, y1: 1, bars: outcomeBars(s, c?.bool),
               ticks: ['True', 'False', 'Int', 'Real', 'Other'].map((l, i) => [2 * i + 1, l]) }) :
    h(Chart, { x0: 0, x1: 10, y1: 1, ticks: [],
               message: ['Click run to execute', 'the simulation'] })
  const ib = d.int ? intBars(s, d.int, c?.int) : []
  const [ia, iz] = d.int ?? [-5, 5]
  const rb = d.real ? realBars(s, bins, d.real) : []
  const [ra, rz] = d.real ?? [-1, 1]
  const line = d.real && c?.real?.map((y, i, ys) => [ra + (rz - ra) * i / (ys.length - 1), y])
  const ticks = (a, z) => [[a, fmt(a)], [(a + z) / 2, fmt((a + z) / 2)], [z, fmt(z)]]
  const empty = (kind, domain) => !ran ? [] :
    s[kind === 'Int' ? 'ints' : 'reals'].length === 0 ? [`no ${kind} results`] :
    domain ? [] : ['too wide a range to draw']
  return h('div', { style: { display: 'grid', gap: '8px', marginTop: '8px',
      gridTemplateColumns: 'repeat(auto-fit, minmax(max(160px, calc((100% - 16px) / 3)), 1fr))' } },
    h(Square, { title: 'Outcomes',
      footer: data?.error ? h('span', { className: 'red' }, data.error) :
              s.failure ? `first failure: ${s.failure}` : '' },
      outcomes),
    h(Square, { title: 'Int', footer: c?.notes?.join(' ') ?? '' },
      h(Chart, { x0: ia, x1: iz, y1: top(ib), bars: ib, ticks: ticks(ia, iz),
                 message: empty('Int', d.int) })),
    h(Square, { title: 'Real',
      footer: h('label', { style: { display: 'flex', justifyContent: 'center',
                                    alignItems: 'center', gap: '0.5em', height: '100%',
                                    // Not the footer's: a taller box would be clipped.
                                    lineHeight: 'normal' } },
        'Bins',
        // The slider stops at `maxSlider` bins; the box takes any number.
        h('input', {
          type: 'range', min: 1, max: maxSlider, value: Math.min(bins, maxSlider),
          style: { flex: 1, minWidth: 0, accentColor: fg },
          onChange: e => editBins(e.target.value) }),
        h('input', {
          type: 'text', inputMode: 'numeric', value: binsText, style: { ...control, width: '5em' },
          onChange: e => editBins(e.target.value) })) },
      h(Chart, { x0: ra, x1: rz, y1: top(rb, line), bars: rb, line, ticks: ticks(ra, rz),
                 message: empty('Real', d.real) })))
}

// `text` as a positive integer, or `undefined`.
function positive(text) {
  const k = Number(text)
  return Number.isInteger(k) && k >= 1 ? k : undefined
}

const control = { color: fg, background: bg, border: `1px solid ${fg}`, borderRadius: '2px',
                  font: 'inherit', padding: '1px 4px' }

// The state of widgets off screen: the infoview unmounts a widget whenever it leaves the screen,
// but keeps this module. Keyed by `stateKey`, the most recently saved last.
const saved = new Map()

// Save `state` under `key`, keeping at most `max` widgets.
function save(key, state, max) {
  saved.delete(key)
  if (max > 0) saved.set(key, state)
  while (saved.size > max) saved.delete(saved.keys().next().value)
}

// A new `stateKey` is another `#sample`: start afresh.
export default function Sample(props) {
  return h(Widget, { ...props, key: props.stateKey })
}

// `engine`, `runs` and `bins` are the values the controls start with, unless the widget was saved.
function Widget(props) {
  const { job, title, engines, stateKey, maxSaved } = props
  const rs = useRpcSession()
  const [was] = React.useState(() => saved.get(stateKey))
  const [engine, setEngine] = React.useState(was?.engine ?? props.engine)
  const [runs, setRuns] = React.useState(was?.runs ?? String(props.runs))
  // The text in the bins box, and the last valid number in it.
  const [binsText, setBinsText] = React.useState(was?.binsText ?? String(props.bins))
  const [bins, setBins] = React.useState(was?.bins ?? props.bins)
  const editBins = text => { setBinsText(text); const k = positive(text); if (k) setBins(k) }
  // 'idle', 'running', 'paused' or 'done'. Unmounting stops a run, so a saved run is paused.
  const [status, setStatus] =
    React.useState(was?.status === 'running' ? 'paused' : was?.status ?? 'idle')
  // The runs so far: `{ engine, target, summary, domains, curves, error }`.
  const [data, setData] = React.useState(was?.data ?? null)
  React.useEffect(() => save(stateKey, { engine, runs, binsText, bins, status, data }, maxSaved),
    [stateKey, maxSaved, engine, runs, binsText, bins, status, data])
  // The active run: `{ ac, stop }`, which abort its requests and stop its process. Only the active
  // run may set the state.
  const active = React.useRef(null)
  function halt() {
    active.current?.ac.abort()
    active.current?.stop?.()
    active.current = null
  }
  React.useEffect(() => halt, [])

  const n = Number(runs)
  const valid = positive(runs) !== undefined
  const running = status === 'running'

  function pause() {
    halt()
    setStatus('paused')
  }

  async function play() {
    const resume = status === 'paused' && data?.engine === engine
    let state = resume ? { ...data, target: n, error: undefined } :
                         { engine, target: n, summary: noRuns, domains: {} }
    setData(state)
    if (state.summary.runs >= n) { setStatus('done'); return }
    const ac = new AbortController(), me = { ac }
    active.current = me
    const current = () => active.current === me
    const call = (method, params) =>
      rs.call(`ProbLang.Interp.Sample.${method}`, params, { abortSignal: ac.signal })
    setStatus('running')
    let run
    try {
      run = await call('startSample', { job, engine, runs: n - state.summary.runs })
      me.stop = () => rs.call('ProbLang.Interp.Sample.stopSample', { run }).catch(() => {})
      for (;;) {
        if (!current()) return
        const chunk = await call('nextChunk', { run })
        if (!current()) return
        // The end of the run: the server's `null` can arrive as `undefined`.
        if (chunk == null) break
        if (!(chunk.runs > 0)) throw new Error('problang-sample reported no runs')
        const summary = merge(state.summary, chunk)
        const d = domains(summary)
        let curves = state.curves
        if (!curves || JSON.stringify(d) !== JSON.stringify(state.domains)) {
          const r = await call('sampleCurves',
            { job, intRange: d.int && [d.int[0], d.int[1] - 1], realRange: d.real })
          if (!current()) return
          curves = { bool: floats(r.bool), int: floats(r.int), real: floats(r.real),
                     notes: r.notes }
        }
        state = { ...state, summary, domains: d, curves }
        setData(state)
      }
      setStatus('done')
    } catch (err) {
      if (current()) {
        setData({ ...state, error: mapRpcError(err).message })
        setStatus(state.summary.runs > 0 ? 'paused' : 'idle')
      }
    } finally {
      // Stopping twice is harmless.
      me.stop?.()
      if (current()) active.current = null
    }
  }

  const target = running || status === 'done' || !valid ? data?.target ?? 0 : n
  const done = data?.summary.runs ?? 0
  const row = { display: 'flex', alignItems: 'center', gap: '0.75em', marginBottom: '6px' }
  const icon = running ?
    [h('rect', { key: 0, x: 3, y: 2, width: 3.5, height: 12 }),
     h('rect', { key: 1, x: 9.5, y: 2, width: 3.5, height: 12 })] :
    [h('path', { key: 0, d: 'M4 2 L14 8 L4 14 Z' })]
  return h('details', { open: true },
    h('summary', { className: 'mv2 pointer' }, title),
    h('div', { className: 'ml1' },
      h('div', { style: row },
        h('label', null, 'Engine ', h('select', {
          value: engine, disabled: running, style: control,
          onChange: e => setEngine(e.target.value) },
          engines.map(e => h('option', { key: e, value: e }, e)))),
        h('label', null, 'Runs ', h('input', {
          type: 'number', min: 1, step: 1, value: runs, disabled: running,
          style: { ...control, width: '7em' }, onChange: e => setRuns(e.target.value) }))),
      h('div', { style: row },
        h('button', {
          onClick: running ? pause : play, disabled: !running && !valid,
          title: running ? 'Pause' : 'Play',
          style: { ...control, width: '26px', height: '22px', padding: 0, display: 'flex',
                   alignItems: 'center', justifyContent: 'center',
                   opacity: !running && !valid ? 0.4 : 1 } },
          h('svg', { width: 12, height: 12, viewBox: '0 0 16 16', fill: 'currentColor' }, icon)),
        h('div', { style: { flex: 1, height: '8px', border: `1px solid ${fg}` } },
          h('div', { style: { width: `${target ? 100 * Math.min(1, done / target) : 0}%`,
                              height: '100%', background: fg } })),
        h('span', { style: { fontVariantNumeric: 'tabular-nums', textAlign: 'right',
                             minWidth: `${2 * String(target).length + 3}ch` } },
          `${done} / ${target}`)),
      h(Charts, { data, bins, binsText, editBins })))
}
"#

/-- The options of a `#sample` command, with their defaults. -/
structure Options where
  /-- The widget's title. -/
  title : String := "Samples"
  /-- The engine the widget starts with. -/
  engine : String := (engines.map (·.1))[0]?.getD ""
  /-- The number of runs the widget starts with. -/
  runs : Nat := 10000
  /-- The number of bins the real histogram starts with. -/
  bins : Nat := 30

register_option sample.maxSaved : Nat := {
  defValue := 16
  descr := "how many `#sample` widgets keep their charts and controls while off screen. Each \
    keeps every result of its runs, so this bounds the infoview's memory; 0 keeps none."
}

/-- The session set by the last `#sample_session`, if any. -/
initialize sessionExt : EnvExtension (Option Nat) ← registerEnvExtension (pure none)

/-- The props of `sampleWidget`. -/
structure Props where
  job : WithRpcRef Job
  /-- Identifies the `#sample` command, for keeping its widget's state. -/
  stateKey : String
  /-- The value of `sample.maxSaved`. -/
  maxSaved : Nat
  engines : Array String
  title : String
  engine : String
  runs : Nat
  bins : Nat
  deriving RpcEncodable

unsafe def evalTermUnsafe (α : Type) (type : Expr) (t : Term) : TermElabM α :=
  Term.withoutErrToSorry <| Term.evalTerm α type t

/-- Evaluate `t : type`. -/
@[implemented_by evalTermUnsafe]
opaque evalTerm (α : Type) (type : Expr) (t : Term) : TermElabM α

/-- An option of `#sample`: `title`, `engine`, `runs`, `bins`, or a curve `boolFun`, `intFun`
or `realFun`, as in `runs := 100000`, optionally followed by a comma. -/
syntax sampleOption := ident " := " term ","?

/-- `#sample e` shows a widget that runs `e : Exp Float` many times and plots the results.

Options go after `with`, one per line or separated by commas: `title := s` (default
`"Samples"`), `engine := s` (default `"tacoma"`), `runs := n` (default `10000`), `bins := n`
(default `30`), and curves `boolFun := f`, `intFun := f` and `realFun := f` to draw over the
charts. For example `#sample e with title := "Uniform", runs := 100000, realFun := fun _ => 1`.
See `ProbLangSampleWidget.lean`. -/
syntax (name := sampleCmd) "#sample " term (" with " many1Indent(sampleOption))? : command

@[command_elab sampleCmd]
def elabSample : Command.CommandElab
  | stx@`(#sample%$tk $e $[with $options*]?) => Command.liftTermElabM do
    let float := mkConst ``Float
    let mut job : Job := { program := ← evalTerm _ (mkApp (.const ``Exp [0]) float) e }
    let mut opts : Options := {}
    let mut seen : Array Name := #[]
    for option in options.getD #[] do
      let `(sampleOption| $k:ident := $f $[,]?) := option | throwUnsupportedSyntax
      if seen.contains k.getId then throwErrorAt k "duplicate option {k}"
      seen := seen.push k.getId
      let curve (α : Type) (dom : Name) : TermElabM α := do
        evalTerm α (← mkArrow (mkConst dom) float) f
      let positive : TermElabM Nat := do
        let n ← evalTerm Nat (mkConst ``Nat) f
        if n == 0 then throwErrorAt f "{k} must be positive"
        return n
      match k.getId with
      | `title => opts := { opts with title := ← evalTerm String (mkConst ``String) f }
      | `engine =>
        let engine ← evalTerm String (mkConst ``String) f
        unless engines.any (·.1 == engine) do
          throwErrorAt f "unknown engine {engine}; the engines are {engines.map (·.1)}"
        opts := { opts with engine }
      | `runs => opts := { opts with runs := ← positive }
      | `bins => opts := { opts with bins := ← positive }
      | `boolFun => job := { job with boolCurve? := some (← curve _ ``Bool) }
      | `intFun => job := { job with intCurve? := some (← curve _ ``Int) }
      | `realFun => job := { job with realCurve? := some (← curve _ ``Float) }
      | _ => throwErrorAt k
        "expected `title`, `engine`, `runs`, `bins`, `boolFun`, `intFun` or `realFun`"
    let props : Props := {
      job := ← WithRpcRef.mk job, engines := engines.map (·.1)
      -- The same command in the same file and session, whatever its layout.
      stateKey := toString (hash (← getFileName, sessionExt.getState (← getEnv), toString stx))
      maxSaved := sample.maxSaved.get (← getOptions)
      title := opts.title, engine := opts.engine, runs := opts.runs, bins := opts.bins }
    let wi ← Widget.WidgetInstance.ofHash (hash sampleWidget.javascript) (rpcEncode props)
    logInfoAt tk (.ofWidget wi "#sample: open the infoview to run it")
  | _ => throwUnsupportedSyntax

/-- `#sample_session` starts a new session for the `#sample` widgets after it: they forget what
they kept whenever it is elaborated again, as when the file is reloaded. Put it at the top of the
file. `#sample_session with maxSaved := n` also sets `sample.maxSaved` to `n`, like `set_option`,
for the rest of the file. -/
syntax (name := sampleSessionCmd) "#sample_session" (" with " many1Indent(sampleOption))? : command

@[command_elab sampleSessionCmd]
def elabSampleSession : Command.CommandElab
  | `(#sample_session $[with $options*]?) => do
    modifyEnv (sessionExt.setState · (some (← IO.monoNanosNow)))
    let mut seen := false
    for option in options.getD #[] do
      let `(sampleOption| $k:ident := $v $[,]?) := option | throwUnsupportedSyntax
      unless k.getId == `maxSaved do throwErrorAt k "expected `maxSaved`"
      if seen then throwErrorAt k "duplicate option {k}"
      seen := true
      let n ← Command.liftTermElabM (evalTerm Nat (mkConst ``Nat) v)
      Command.modifyScope fun scope => { scope with opts := sample.maxSaved.set scope.opts n }
  | _ => throwUnsupportedSyntax

end ProbLang.Interp.Sample
