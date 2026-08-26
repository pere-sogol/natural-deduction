/* The editor's shell: start Python, forward events, set what comes back.
 *
 * All the logic is in Python.  This file owns three pieces of state of its
 * own -- the rule the palette is holding, the block the pointer is
 * dragging, and whether an inline editor is open -- and nothing else; even
 * the selected slot lives in the session, so that a refresh of the view
 * cannot disagree with it.
 */
"use strict";

let dispatch = null;   // the Python entry point
let state = null;      // the last view
let held = null;       // a rule from the palette: {kind: "rule", value}
let drag = null;       // a block under the pointer; see grab() for its shape
let dragged = false;   // the last gesture moved something: swallow its click
let editing = false;   // an inline editor is open; do not repaint under it

const $ = id => document.getElementById(id);

/* -- talking to Python ---------------------------------------------------- */

function send(action) {
  if (!dispatch) return;
  try {
    state = JSON.parse(dispatch(JSON.stringify(action)));
  } catch (error) {
    $("notice").textContent = "the proof checker stopped: " + error;
    throw error;
  }
  paint();
}

/* -- setting the page ------------------------------------------------------ */

function paint() {
  if (editing) return;
  $("sequent").textContent = state.sequent || "set a goal…";

  /* A slot with a sentence in it is not a gap any more -- it is an
   * assumption, and the tracker counts it as one.  Only the blank ones
   * are still work of the sort "type something here". */
  const status = $("status");
  const loose = state.assumptions.extra.length;
  if (state.solved) {
    status.textContent = "proved";
    status.className = "solved";
  } else if (state.blankSlots.length) {
    status.textContent = state.blankSlots.length + " slot" +
      (state.blankSlots.length === 1 ? "" : "s") + " to fill";
    status.className = "open";
  } else if (loose) {
    status.textContent = loose + " open assumption" + (loose === 1 ? "" : "s");
    status.className = "open";
  } else {
    status.textContent = "";
    status.className = "";
  }

  $("undo").disabled = !state.canUndo;
  $("redo").disabled = !state.canRedo;
  $("notice").textContent = state.notice || "";
  $("hint").style.display = state.cards.length ? "none" : "";

  setPalette(state, $("palette"));
  setRests(state, $("rests"));

  const sheet = $("cards");
  sheet.textContent = "";
  state.cards.forEach(card =>
    sheet.appendChild(setCard(card, card.root === state.provedBy)));

  const focus = state.focus;
  if (focus !== null && focus !== undefined) {
    const found = sheet.querySelector('[data-slot="' + focus + '"]');
    if (found) found.classList.add("focused");
  }
  paintContext();

  const chooser = $("exercises");
  if (!chooser.options.length) {
    chooser.appendChild(new Option("Choose a problem…", ""));
    state.exercises.forEach(e =>
      chooser.appendChild(new Option(e.title + "   " + e.sequent, e.key)));
  }
}

/* What may be assumed where the cursor is.  Advisory: a slot can perfectly
 * well be closed by something resting on other assumptions, and the proof
 * still stands with that assumption showing as open at the root. */
function paintContext() {
  const context = $("context");
  context.textContent = "";
  const focus = state.focus;
  if (focus === null || focus === undefined) return;
  const available = state.contexts[String(focus)] || [];
  if (!available.length) return;
  context.appendChild(el("b", null, "May assume here:"));
  available.forEach(text => {
    const chip = el("button", "chip", text);
    chip.title = "Fill this slot by assuming " + text;
    chip.onclick = () =>
      send({ op: "place", rule: "Assumption", slot: focus, text: text });
    context.appendChild(chip);
  });
}

/* -- editing a slot -------------------------------------------------------- */

function editSlot(span) {
  const node = Number(span.dataset.slot);
  editing = true;
  openEditor(span, span.dataset.text,
    text => { editing = false; send({ op: "set", node: node, text: text }); },
    () => { editing = false; paint(); });
}

function editParam(chip) {
  const node = Number(chip.dataset.node);
  const name = chip.dataset.param;
  const host = chip.querySelector(".v");
  editing = true;
  openEditor(host, chip.dataset.text,
    text => {
      editing = false;
      send({ op: "param", node: node, name: name, text: text });
    },
    () => { editing = false; paint(); });
}

/* -- putting a rule down --------------------------------------------------- */

function place(ruleName, target, x, y) {
  if (target !== null && target !== undefined) {
    send({ op: "place", rule: ruleName, slot: target });
  } else {
    send({ op: "place", rule: ruleName, x: x, y: y });
  }
}

function sheetPoint(event) {
  const sheet = $("sheet");
  const box = sheet.getBoundingClientRect();
  return {
    x: Math.max(0, Math.round(event.clientX - box.left + sheet.scrollLeft)),
    y: Math.max(0, Math.round(event.clientY - box.top + sheet.scrollTop)),
  };
}

/* -- picking a block up ---------------------------------------------------- */

/* One gesture, two jobs, and where it starts decides which: on the bar of
 * a step or on the handle beside it, it pulls that branch out of the block
 * it is in; anywhere else on the card, it slides the whole card.  Nothing
 * happens at all until the pointer has travelled, so a click that lands on
 * a sentence still selects it and a second still opens it for typing.
 *
 * This is done with pointer events rather than the browser's own drag and
 * drop, which cannot make a whole card draggable without also making the
 * text inside it unselectable in the inline editor -- and which gives the
 * block no way to follow the pointer while it is being carried. */
const THRESHOLD = 5;

function grab(event) {
  const card = event.target.closest(".card");
  if (!card) return null;
  const root = Number(card.dataset.root);
  const handle = event.target.closest(".pull, .bar");
  const branch = handle ? handle.closest(".inf") : null;

  /* The block's own bar has no branch above it to pull off -- what is over
   * it is the whole card -- so grabbing that slides the card like the rest
   * of it does. */
  const pulling = branch && Number(branch.dataset.id) !== root;
  const from = pulling ? branch : card;
  const box = from.getBoundingClientRect();
  return {
    kind: pulling ? "branch" : "card",
    id: pulling ? Number(branch.dataset.id) : root,
    card: card, from: from, live: false,
    dx: event.clientX - box.left, dy: event.clientY - box.top,
    origin: { x: event.clientX, y: event.clientY },
  };
}

/* A card carries itself.  A branch cannot -- it is set inside a figure
 * that would reflow around the gap -- so it travels as a copy, and the
 * block it is leaving keeps its shape until the pointer says where. */
function lift(hold) {
  hold.live = true;
  document.body.classList.add("grabbing");
  if (hold.kind === "card") {
    hold.moving = hold.card;
    hold.card.classList.add("lifted");
    return;
  }
  const ghost = el("div", "ghost");
  ghost.appendChild(hold.from.cloneNode(true));
  document.body.appendChild(ghost);
  const inside = ghost.firstChild.getBoundingClientRect();
  const outside = ghost.getBoundingClientRect();
  hold.pad = { x: inside.left - outside.left, y: inside.top - outside.top };
  hold.moving = ghost;
  hold.from.classList.add("pulling");
}

function slide(hold, event) {
  if (hold.kind === "card") {
    const at = sheetPoint(event);
    hold.moving.style.left = Math.max(0, at.x - hold.dx) + "px";
    hold.moving.style.top = Math.max(0, at.y - hold.dy) + "px";
  } else {
    hold.moving.style.left = (event.clientX - hold.dx - hold.pad.x) + "px";
    hold.moving.style.top = (event.clientY - hold.dy - hold.pad.y) + "px";
  }
}

/* The slot under the pointer, if it is one this block could go into.  What
 * is being carried has its pointer events off, so the page underneath
 * answers honestly about what is beneath it. */
function slotUnder(hold, event) {
  const under = document.elementFromPoint(event.clientX, event.clientY);
  const slot = under ? under.closest('.inf[data-kind="slot"] .slot') : null;
  return slot && !hold.from.contains(slot) ? slot : null;
}

function mark(slot) {
  document.querySelectorAll(".slot.dropping")
    .forEach(n => n.classList.remove("dropping"));
  if (slot) slot.classList.add("dropping");
}

/* Putting it down.  ``keep`` is false when the gesture was called off, and
 * then the repaint puts the card back where the model still says it is. */
function release(hold, event, keep) {
  /* Asked before the block is put down, because it is what is being
   * carried that is in the way: it answers with pointer events off. */
  const slot = hold.live && keep ? slotUnder(hold, event) : null;

  document.body.classList.remove("grabbing");
  document.querySelectorAll(".lifted, .pulling")
    .forEach(n => n.classList.remove("lifted", "pulling"));
  if (hold.kind === "branch" && hold.moving) hold.moving.remove();
  mark(null);
  if (!hold.live) return;
  dragged = true;
  if (!keep) { paint(); return; }

  const target = slot ? Number(slot.dataset.slot) : null;
  const at = sheetPoint(event);
  if (hold.kind === "card") {
    if (target !== null) send({ op: "attach", slot: target, source: hold.id });
    else send({ op: "move", root: hold.id,
                x: Math.max(0, at.x - hold.dx), y: Math.max(0, at.y - hold.dy) });
    return;
  }
  send({ op: "detach", node: hold.id,
         x: Math.max(0, at.x - hold.dx - hold.pad.x),
         y: Math.max(0, at.y - hold.dy - hold.pad.y) });
  /* Pulled out of one block and put straight into another: two operations,
   * because the sheet has no single one for it.  The branch keeps its own
   * number when it comes off, so the second knows what to look for. */
  if (target !== null) send({ op: "attach", slot: target, source: hold.id });
}

/* Clicking the handle instead of dragging it.  The branch still has to go
 * somewhere, so it goes beside the block it came out of, at its own
 * height -- never on top of it, because a block underneath another one
 * looks like a block that has been thrown away. */
function pullOut(handle) {
  const sheet = $("sheet");
  const card = handle.closest(".card").getBoundingClientRect();
  const branch = handle.closest(".inf").getBoundingClientRect();
  const box = sheet.getBoundingClientRect();
  send({
    op: "detach", node: Number(handle.dataset.pull),
    x: Math.round(card.right - box.left + sheet.scrollLeft + 24),
    y: Math.max(0, Math.round(branch.top - box.top + sheet.scrollTop - 12)),
  });
}

/* -- events ---------------------------------------------------------------- */

function wire() {
  const palette = $("palette");
  const sheet = $("sheet");

  /* Clicking a rule arms it; the next click on a slot or on the sheet puts
   * it there.  The same two actions as dragging, for a trackpad or a
   * keyboard, and the only way to do it on a touch screen. */
  palette.addEventListener("click", event => {
    const button = event.target.closest("[data-rule]");
    if (!button) return;
    const already = button.classList.contains("armed");
    palette.querySelectorAll(".armed").forEach(n => n.classList.remove("armed"));
    if (!already) {
      button.classList.add("armed");
      held = { kind: "rule", value: button.dataset.rule, sticky: true };
    } else {
      held = null;
    }
  });

  palette.addEventListener("dragstart", event => {
    const button = event.target.closest("[data-rule]");
    if (!button) return;
    held = { kind: "rule", value: button.dataset.rule };
    button.classList.add("dragging");
    event.dataTransfer.effectAllowed = "copy";
    event.dataTransfer.setData("text/plain", button.dataset.rule);
  });

  document.addEventListener("dragend", () => {
    document.querySelectorAll(".dragging, .dropping")
      .forEach(n => n.classList.remove("dragging", "dropping"));
    if (held && !held.sticky) held = null;
  });

  /* A card is picked up anywhere on it, and a branch by the bar of its
   * step or the handle beside it.  Both land on the sheet as a card of
   * their own, or in a slot if one is under the pointer at the end. */
  sheet.addEventListener("pointerdown", event => {
    if (event.button !== 0) return;
    dragged = false;
    /* An open editor commits on the way out and the view is repainted
     * under us, so there would be nothing left to carry. */
    if (editing) return;
    if (event.target.closest("input, .bin, .param")) return;
    const hold = grab(event);
    if (!hold) return;
    hold.pointer = event.pointerId;
    drag = hold;
    sheet.setPointerCapture(event.pointerId);
  });

  sheet.addEventListener("pointermove", event => {
    const hold = drag;
    if (!hold || event.pointerId !== hold.pointer) return;
    if (!hold.live) {
      const gone = Math.abs(event.clientX - hold.origin.x)
                 + Math.abs(event.clientY - hold.origin.y);
      if (gone < THRESHOLD) return;
      lift(hold);
    }
    slide(hold, event);
    mark(slotUnder(hold, event));
  });

  sheet.addEventListener("pointerup", event => {
    const hold = drag;
    if (!hold || event.pointerId !== hold.pointer) return;
    drag = null;
    release(hold, event, true);
  });

  /* Either of these can be the end of it, and the second is the one that
   * fires when the pointer is taken away rather than lifted -- without it
   * a card could be left carried, with nothing to put it down. */
  ["pointercancel", "lostpointercapture"].forEach(name =>
    sheet.addEventListener(name, event => {
      const hold = drag;
      if (!hold || event.pointerId !== hold.pointer) return;
      drag = null;
      release(hold, event, false);
    }));

  sheet.addEventListener("dragover", event => {
    if (!held) return;
    event.preventDefault();
    const slot = event.target.closest('.inf[data-kind="slot"] .slot');
    document.querySelectorAll(".slot.dropping")
      .forEach(n => n.classList.remove("dropping"));
    if (slot) slot.classList.add("dropping");
  });

  /* Only a rule from the palette arrives this way now; blocks already on
   * the sheet are carried by the pointer instead. */
  sheet.addEventListener("drop", event => {
    if (!held) return;
    event.preventDefault();
    document.querySelectorAll(".dropping").forEach(n =>
      n.classList.remove("dropping"));
    const where = sheetPoint(event);
    const slot = event.target.closest('.inf[data-kind="slot"] .slot');
    place(held.value, slot ? Number(slot.dataset.slot) : null, where.x, where.y);
    if (!held.sticky) held = null;
    palette.querySelectorAll(".armed").forEach(n => n.classList.remove("armed"));
  });

  sheet.addEventListener("click", event => {
    if (event.target.closest("input")) return;
    /* The gesture that ended here moved a block, so whatever it finished
     * on top of was not being clicked. */
    if (dragged) { dragged = false; return; }

    const bin = event.target.closest("[data-bin]");
    if (bin) { send({ op: "delete", node: Number(bin.dataset.bin) }); return; }

    const pull = event.target.closest("[data-pull]");
    if (pull) { pullOut(pull); return; }

    const chip = event.target.closest("[data-param]");
    if (chip) { editParam(chip); return; }

    const armed = held && held.kind === "rule" ? held.value : null;
    const disarm = () => {
      held = null;
      palette.querySelectorAll(".armed").forEach(n => n.classList.remove("armed"));
    };

    const slot = event.target.closest(".slot");
    if (slot) {
      const node = Number(slot.dataset.slot);
      if (armed) { disarm(); place(armed, node, 0, 0); return; }
      /* First click selects, second opens the editor: a slot is also a
       * drop target and a selection, and typing into it on the way past
       * would make both of those harder to hit. */
      if (state.focus === node) editSlot(slot);
      else send({ op: "focus", node: node });
      return;
    }

    if (event.target.closest(".card")) return;
    if (armed) {
      const where = sheetPoint(event);
      disarm();
      place(armed, null, where.x, where.y);
      return;
    }
    send({ op: "focus", node: null });
  });

  /* Hovering an inference lights every leaf it discharges.  One step can
   * close several -- As(π) is a set of sentences -- and that is the thing
   * students most often miss. */
  sheet.addEventListener("mouseover", event => {
    const bar = event.target.closest(".bar[data-discharge]");
    if (!bar) return;
    const number = bar.dataset.discharge;
    bar.classList.add("lit");
    bar.closest(".card")
      .querySelectorAll('.slot[data-discharge="' + number + '"]')
      .forEach(n => n.classList.add("lit"));
  });
  sheet.addEventListener("mouseout", () => {
    document.querySelectorAll(".lit").forEach(n => n.classList.remove("lit"));
  });

  /* An assumption in the panel goes somewhere: clicking selects the leaf
   * it was made at, and hovering lights every leaf carrying that sentence
   * at once -- which is the whole of why As(π) is a set of sentences and
   * not of nodes, shown rather than explained. */
  const rests = $("rests");
  rests.addEventListener("click", event => {
    const row = event.target.closest("[data-nodes]");
    if (!row) return;
    send({ op: "focus", node: Number(row.dataset.nodes.split(",")[0]) });
  });
  rests.addEventListener("mouseover", event => {
    const row = event.target.closest("[data-nodes]");
    if (!row) return;
    row.classList.add("lit");
    row.dataset.nodes.split(",").forEach(id => {
      const found = $("cards").querySelector('.slot[data-slot="' + id + '"]');
      if (found) found.classList.add("lit");
    });
  });
  rests.addEventListener("mouseout", () => {
    document.querySelectorAll(".lit").forEach(n => n.classList.remove("lit"));
  });

  $("sequent").onclick = () => {
    const goal = window.prompt(
      "What are you proving?  Premises first, separated by commas, then ⊢.\n" +
      "For example:  P -> Q, Q -> R  |-  P -> R",
      state.premises.concat([]).join(", ") +
        (state.premises.length ? " |- " : "") + (state.goal || ""));
    if (goal === null) return;
    const parts = goal.split(/\|-|⊢|\\vdash/);
    const left = parts.length > 1 ? parts[0] : "";
    const right = parts.length > 1 ? parts[1] : parts[0];
    send({
      op: "new", goal: right.trim(),
      premises: left.split(",").map(s => s.trim()).filter(s => s),
    });
  };

  $("undo").onclick = () => send({ op: "undo" });
  $("redo").onclick = () => send({ op: "redo" });
  $("clear").onclick = () => send({ op: "clear" });
  $("exercises").onchange = event => {
    if (event.target.value) send({ op: "exercise", key: event.target.value });
  };
  $("share").onclick = async () => {
    const url = location.origin + location.pathname + "#" + state.fragment;
    try {
      await navigator.clipboard.writeText(url);
      $("notice").textContent = "link copied";
    } catch (error) {
      location.hash = state.fragment;
      $("notice").textContent = "link is in the address bar";
    }
  };

  document.addEventListener("keydown", event => {
    if (event.target.tagName === "INPUT" || event.target.tagName === "SELECT") return;
    const meta = event.metaKey || event.ctrlKey;
    if (meta && event.key.toLowerCase() === "z") {
      event.preventDefault();
      send({ op: event.shiftKey ? "redo" : "undo" });
    } else if (event.key === "Escape") {
      if (drag) {
        const hold = drag;
        drag = null;
        release(hold, event, false);
        return;
      }
      held = null;
      document.querySelectorAll(".armed").forEach(n => n.classList.remove("armed"));
      send({ op: "focus", node: null });
    } else if (event.key === "Enter" && state.focus !== null) {
      const slot = document.querySelector('.slot[data-slot="' + state.focus + '"]');
      if (slot) { event.preventDefault(); editSlot(slot); }
    } else if ((event.key === "Backspace" || event.key === "Delete")
               && state.focus !== null) {
      event.preventDefault();
      send({ op: "delete", node: state.focus });
    }
  });
}

/* -- boot ------------------------------------------------------------------ */

/* The sources are fetched fresh every time, never from the browser's cache.
 *
 * ``web/serve.py`` sends ``Cache-Control: no-store`` for exactly this reason,
 * but the page must not depend on being served by it: any other static server
 * -- ``python3 -m http.server``, say -- sends no freshness header at all, and a
 * browser then caches on a heuristic of its own. Files edited at different
 * times get different heuristic lifetimes, so a reload can mix a cached module
 * with a fresh one: half of ``nd`` from this morning and half from last night,
 * which registers rules the rest of the code no longer knows about. Asking for
 * ``no-store`` here settles it wherever the page is served from. */
function load(path) {
  return fetch(path, { cache: "no-store" });
}

async function boot() {
  const say = text => { $("bootmsg").textContent = text; };
  say("Downloading Python…");
  const pyodide = await loadPyodide();

  say("Loading the proof checker…");
  const files = await (await load("manifest.json")).json();
  await Promise.all(files.map(async path => {
    const source = await (await load("../" + path)).text();
    const directory = "/lib/" + path.slice(0, path.lastIndexOf("/"));
    pyodide.FS.mkdirTree(directory);
    pyodide.FS.writeFile("/lib/" + path, source);
  }));

  const bootstrap = await (await load("bootstrap.py")).text();
  pyodide.runPython(bootstrap);
  dispatch = pyodide.globals.get("dispatch");

  wire();

  const fragment = location.hash.slice(1);
  if (fragment) send({ op: "load-fragment", fragment: fragment });
  else send({ op: "exercise", key: "identity" });

  $("boot").classList.add("done");
}

boot().catch(error => {
  $("bootmsg").textContent =
    "Could not start: " + error + " — is this page being served over http?";
});
