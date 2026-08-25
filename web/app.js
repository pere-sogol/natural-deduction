/* The editor's shell: start Python, forward events, set what comes back.
 *
 * All the logic is in Python.  This file owns two pieces of state of its
 * own -- what the pointer is dragging, and whether an inline editor is
 * open -- and nothing else; even the selected slot lives in the session,
 * so that a refresh of the view cannot disagree with it.
 */
"use strict";

let dispatch = null;   // the Python entry point
let state = null;      // the last view
let held = null;       // {kind: "rule"|"card"|"branch", value, dx, dy}
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

  const status = $("status");
  if (state.solved) {
    status.textContent = "proved";
    status.className = "solved";
  } else if (state.openSlots.length) {
    status.textContent = state.openSlots.length + " slot" +
      (state.openSlots.length === 1 ? "" : "s") + " to fill";
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

  /* A card is moved by its grip; a branch is pulled out of a block by
   * dragging its bar.  Both land on the sheet as a card of their own. */
  sheet.addEventListener("dragstart", event => {
    const grip = event.target.closest("[data-grip]");
    if (grip) {
      const card = grip.closest(".card");
      const box = card.getBoundingClientRect();
      held = {
        kind: "card", value: Number(grip.dataset.grip),
        dx: event.clientX - box.left, dy: event.clientY - box.top,
      };
      card.classList.add("dragging");
      event.dataTransfer.effectAllowed = "move";
      event.dataTransfer.setData("text/plain", grip.dataset.grip);
      return;
    }
    const bar = event.target.closest(".bar");
    if (!bar) return;
    const inference = bar.closest(".inf");
    held = { kind: "branch", value: Number(inference.dataset.id), dx: 0, dy: 0 };
    inference.classList.add("dragging");
    event.dataTransfer.effectAllowed = "move";
    event.dataTransfer.setData("text/plain", inference.dataset.id);
  });

  sheet.addEventListener("dragover", event => {
    if (!held) return;
    event.preventDefault();
    const slot = event.target.closest('.inf[data-kind="slot"] .slot');
    document.querySelectorAll(".slot.dropping")
      .forEach(n => n.classList.remove("dropping"));
    if (slot) slot.classList.add("dropping");
  });

  sheet.addEventListener("drop", event => {
    if (!held) return;
    event.preventDefault();
    document.querySelectorAll(".dropping").forEach(n =>
      n.classList.remove("dropping"));
    const where = sheetPoint(event);
    const slot = event.target.closest('.inf[data-kind="slot"] .slot');
    const target = slot ? Number(slot.dataset.slot) : null;

    if (held.kind === "rule") {
      place(held.value, target, where.x, where.y);
    } else if (held.kind === "card") {
      if (target !== null) send({ op: "attach", slot: target, source: held.value });
      else send({
        op: "move", root: held.value,
        x: where.x - (held.dx || 0), y: where.y - (held.dy || 0),
      });
    } else if (held.kind === "branch") {
      send({ op: "detach", node: held.value, x: where.x, y: where.y });
    }
    if (!held.sticky) held = null;
    palette.querySelectorAll(".armed").forEach(n => n.classList.remove("armed"));
  });

  sheet.addEventListener("click", event => {
    if (event.target.closest("input")) return;

    const bin = event.target.closest("[data-bin]");
    if (bin) { send({ op: "delete", node: Number(bin.dataset.bin) }); return; }

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

async function boot() {
  const say = text => { $("bootmsg").textContent = text; };
  say("Downloading Python…");
  const pyodide = await loadPyodide();

  say("Loading the proof checker…");
  const files = await (await fetch("manifest.json")).json();
  await Promise.all(files.map(async path => {
    const source = await (await fetch("../" + path)).text();
    const directory = "/lib/" + path.slice(0, path.lastIndexOf("/"));
    pyodide.FS.mkdirTree(directory);
    pyodide.FS.writeFile("/lib/" + path, source);
  }));

  const bootstrap = await (await fetch("bootstrap.py")).text();
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
