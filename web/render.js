/* Setting the view.
 *
 * The rule for this file: if a function here would want a unit test, it
 * belongs in Python instead.  Nothing below decides anything about logic.
 * It does not know what a rule is, which slots a block has, what may fill
 * one, or whether anything is proved; it turns the description Python
 * sends into elements, and the elements into events.
 *
 * There are no coordinates either, apart from a card's own place on the
 * sheet.  An inference is a column of premises, bar and conclusion, and
 * the browser measures the type.
 */
"use strict";

function el(tag, cls, text) {
  const node = document.createElement(tag);
  if (cls) node.className = cls;
  if (text !== undefined) node.textContent = text;
  return node;
}

/* A sentence, set from its pieces: italic letters, upright connectives,
 * subscripts lowered.  Python cut it up; the classes are in the CSS. */
function setSentence(sentence) {
  const node = el("span", "slot " + sentence.source);
  sentence.pieces.forEach(piece => node.appendChild(el("span", piece.c, piece.t)));
  if (sentence.open) node.classList.add("open");
  if (sentence.slot !== undefined && sentence.slot !== null) {
    node.dataset.slot = sentence.slot;
  }
  node.dataset.text = sentence.text;
  return node;
}

/* A discharged assumption is bracketed and numbered with the step that
 * closed it -- one number can mark several leaves, which is the thing
 * students most often miss, so hovering the bar lights all of them. */
function setLine(sentence, note) {
  const line = el("div", "line");
  const marked = sentence.discharged !== null && sentence.discharged !== undefined;
  if (marked) line.appendChild(el("span", "brack", "["));
  const body = setSentence(sentence);
  line.appendChild(body);
  if (marked) {
    line.appendChild(el("span", "brack", "]"));
    line.appendChild(el("sup", "mark", String(sentence.discharged)));
    body.dataset.discharge = String(sentence.discharged);
  }
  if (note) line.appendChild(el("span", "note", note));
  return line;
}

function setParams(params, nodeId) {
  const chips = el("div", "params");
  params.forEach(param => {
    const chip = el("div", "param " + param.source);
    chip.appendChild(el("span", "k", param.name));
    const value = el("span", "v");
    param.pieces.forEach(piece => value.appendChild(el("span", piece.c, piece.t)));
    chip.appendChild(value);
    chip.dataset.param = param.name;
    chip.dataset.node = nodeId;
    chip.dataset.text = param.text;
    chip.title = param.description;
    chips.appendChild(chip);
  });
  return chips;
}

function setInference(node) {
  const box = el("div", "inf");
  box.dataset.id = node.id;
  box.dataset.status = node.status;
  box.dataset.kind = node.kind;

  if (node.premises.length) {
    const above = el("div", "prem");
    node.premises.forEach(child => above.appendChild(setInference(child)));
    box.appendChild(above);
  }

  /* A rule with nothing above it -- an assumption, or a = a -- has no
   * bar in the book either; its label goes beside the sentence. */
  if (node.kind === "step" && node.premises.length) {
    const bar = el("div", "bar");
    const label = el("span", "lab", node.label);
    if (node.number !== null && node.number !== undefined) {
      label.appendChild(el("sup", null, ", " + node.number));
      bar.dataset.discharge = String(node.number);
    }
    if (node.message) label.append(" ✗");
    bar.appendChild(label);
    bar.title = node.message || node.rule + " — drag to pull this branch off";
    bar.draggable = true;
    box.appendChild(bar);
  }

  const bare = node.kind === "step" && !node.premises.length;
  box.appendChild(setLine(node.conclusion, bare ? node.label : ""));

  if (node.kind === "step" && node.params.length) {
    box.appendChild(setParams(node.params, node.id));
  }
  if (node.message) box.appendChild(el("div", "why", node.message));
  else if (node.note) box.appendChild(el("div", "why mild", node.note));
  return box;
}

function setCard(card, solution) {
  const box = el("div", "card");
  box.style.left = card.x + "px";
  box.style.top = card.y + "px";
  box.dataset.root = card.root;
  if (card.complete) box.classList.add("complete");
  if (solution) box.classList.add("solution");

  const grip = el("div", "grip");
  grip.draggable = true;
  grip.dataset.grip = card.root;
  box.appendChild(grip);

  const bin = el("button", "bin", "×");
  bin.title = "Take this block off the sheet";
  bin.dataset.bin = card.root;
  box.appendChild(bin);

  box.appendChild(setInference(card.tree));

  if (card.complete) {
    const rests = card.open.length
      ? "proves " + card.conclusion + " from " + card.open.join(", ")
      : "proves " + card.conclusion + ", resting on nothing";
    const tick = el("div", "tick", "✓");
    tick.title = rests;
    box.appendChild(tick);
  }
  return box;
}

/* The palette shows each rule as the figure it puts on the sheet, in the
 * argument order its constructor takes -- which is the reference's, and
 * which surprises people twice: ↔Intro proves the right half first, and
 * ∨Elim takes its disjunction last. */
function setSchema(schema) {
  const box = el("div", "inf");
  if (schema.premises.length) {
    const above = el("div", "prem");
    schema.premises.forEach(premise => {
      const one = el("div", "inf");
      const line = el("div", "line");
      if (premise.brackets) line.appendChild(el("span", "brack", "["));
      line.appendChild(setSentence(premise.conclusion));
      if (premise.brackets) line.appendChild(el("span", "brack", "]"));
      one.appendChild(line);
      above.appendChild(one);
    });
    box.appendChild(above);
  }
  const bar = el("div", "bar");
  box.appendChild(bar);
  const line = el("div", "line");
  line.appendChild(setSentence(schema.conclusion));
  box.appendChild(line);
  return box;
}

function setPalette(state, into) {
  into.textContent = "";
  const groups = [
    ["Assume", rule => rule.group === "leaf"],
    ["Introduce a connective", rule => rule.group === "intro"],
    ["Take one apart", rule => rule.group === "elim"],
  ];
  groups.forEach(([title, pick]) => {
    const rules = state.palette.filter(pick);
    if (!rules.length) return;
    into.appendChild(el("h2", null, title));
    rules.forEach(rule => {
      const button = el("button", "rule");
      button.appendChild(el("span", "tag", rule.label || rule.name));
      const figure = el("span", "fig");
      figure.appendChild(setSchema(rule.schema));
      button.appendChild(figure);
      button.dataset.rule = rule.name;
      button.draggable = true;
      if (!rule.fits) button.classList.add("misfit");
      button.title = rule.summary
        + (rule.caveat ? "\n\n" + rule.caveat : "")
        + (rule.fits ? "" : "\n\nNot for the selected slot: " + rule.why);
      into.appendChild(button);
    });
  });
}

/* The assumption tracker.
 *
 * Every sentence at the top of a step with nothing above it is assumed,
 * and the one question worth asking about it is whether it was given.  So
 * the panel is that question, sorted: what the sequent handed over, what
 * has been helped to besides, and what has been discharged on the way.
 * Python decides all three; nothing here knows what a premise is.
 *
 * A row is a button because it goes somewhere -- clicking it selects the
 * leaf it came from, which on a sheet several blocks wide is the only
 * quick way to find the assumption a verdict is complaining about.
 */
function setRest(row, tone, badge) {
  const line = el("button", "rest");
  line.classList.add(tone);
  const body = el("span", "sent");
  row.pieces.forEach(piece => body.appendChild(el("span", piece.c, piece.t)));
  line.appendChild(body);
  if (badge) line.appendChild(el("span", "count", badge));
  const where = row.nodes.length ? row.nodes : row.closed;
  if (where.length) line.dataset.nodes = where.join(",");
  else line.disabled = true;
  return line;
}

/* ``×3`` counts the leaves, and is left off when there is only one --
 * a bare "1" beside every row is noise, and the interesting number is
 * the one that says a single discharge will close several leaves. */
function restCount(row) {
  const where = row.nodes.length ? row.nodes : row.closed;
  return where.length > 1 ? "×" + where.length : "";
}

function setRests(state, into) {
  into.textContent = "";
  const tracker = state.assumptions;
  into.appendChild(el("h2", null, "Assumptions"));

  if (tracker.verdict) {
    const tone = state.solved ? "verdict good" : "verdict warn";
    into.appendChild(el("div", tone, tracker.verdict));
  }

  const sections = [
    ["Given", tracker.premises, "premise",
     "a premise: assuming it costs nothing"],
    ["Still assuming", tracker.extra, "extra",
     "not a premise — prove it, or discharge it"],
    ["Discharged", tracker.closed, "closed",
     "closed by a step below; it costs nothing now"],
  ];
  sections.forEach(([title, rows, tone, why]) => {
    if (!rows.length) return;
    into.appendChild(el("h3", null, title));
    rows.forEach(row => {
      const unused = tone === "premise" && !row.nodes.length && !row.closed.length;
      const line = setRest(row, unused ? "unused" : tone,
                           unused ? "unused" : restCount(row));
      line.title = unused ? "nothing on the sheet assumes this yet" : why;
      into.appendChild(line);
    });
  });

  if (tracker.blanks.length) {
    const note = el("p", "blanks",
      tracker.blanks.length + " slot" +
      (tracker.blanks.length === 1 ? " is" : "s are") + " still blank");
    into.appendChild(note);
  }
  if (!tracker.premises.length && !tracker.extra.length && !tracker.closed.length) {
    into.appendChild(el("p", "blanks", "Nothing is assumed yet."));
  }
}

/* An input sized to what is in it, so a slot does not jump when it opens.
 * ``commit`` gets the text; ``undo`` puts the sentence back untouched. */
function openEditor(host, text, commit, cancel) {
  const input = el("input");
  input.value = text || "";
  input.autocomplete = "off";
  input.spellcheck = false;
  const size = () => {
    input.style.width = Math.max(5, input.value.length + 2) + "ch";
  };
  size();
  input.oninput = size;
  host.textContent = "";
  host.appendChild(input);
  host.classList.add("editing");
  input.focus();
  input.select();

  let done = false;
  const finish = keep => {
    if (done) return;
    done = true;
    if (keep) commit(input.value);
    else cancel();
  };
  input.onkeydown = event => {
    if (event.key === "Enter") { event.preventDefault(); finish(true); }
    else if (event.key === "Escape") { event.preventDefault(); finish(false); }
    event.stopPropagation();
  };
  input.onblur = () => finish(true);
  return input;
}
