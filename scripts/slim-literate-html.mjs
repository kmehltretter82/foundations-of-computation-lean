#!/usr/bin/env node

import { readdir, readFile, stat, writeFile } from "node:fs/promises";
import path from "node:path";

function usage() {
  console.error(
    [
      "Usage: node scripts/slim-literate-html.mjs [--strip-bindings] [--strip-hovers] SITE_DIR",
      "",
      "Reduces Verso literate HTML size in-place.",
      "Default: remove inline tactic proof states while preserving visible tactic code.",
      "--strip-bindings removes data-binding attributes and disables identifier binding highlights.",
      "--strip-hovers removes data-verso-hover attributes and disables hover doc/type popups.",
    ].join("\n"),
  );
}

function parseArgs(argv) {
  const opts = {
    stripBindings: false,
    stripHovers: false,
    siteDir: null,
  };

  for (const arg of argv) {
    if (arg === "--strip-bindings") {
      opts.stripBindings = true;
    } else if (arg === "--strip-hovers") {
      opts.stripHovers = true;
    } else if (arg === "-h" || arg === "--help") {
      usage();
      process.exit(0);
    } else if (!opts.siteDir) {
      opts.siteDir = arg;
    } else {
      throw new Error(`unexpected argument: ${arg}`);
    }
  }

  if (!opts.siteDir) {
    throw new Error("missing SITE_DIR");
  }

  return opts;
}

async function* htmlFiles(root) {
  const entries = await readdir(root, { withFileTypes: true });
  for (const entry of entries) {
    const fullPath = path.join(root, entry.name);
    if (entry.isDirectory()) {
      yield* htmlFiles(fullPath);
    } else if (entry.isFile() && entry.name.endsWith(".html")) {
      yield fullPath;
    }
  }
}

function skipWhitespace(text, index) {
  while (index < text.length) {
    const c = text.charCodeAt(index);
    if (c !== 9 && c !== 10 && c !== 12 && c !== 13 && c !== 32) break;
    index += 1;
  }
  return index;
}

function tagEnd(text, tagStart) {
  let quote = null;
  for (let i = tagStart + 1; i < text.length; i += 1) {
    const ch = text[i];
    if (quote) {
      if (ch === quote) quote = null;
    } else if (ch === '"' || ch === "'") {
      quote = ch;
    } else if (ch === ">") {
      return i;
    }
  }
  return -1;
}

function isTacticSpanOpen(text, index) {
  if (!text.startsWith("<span", index)) return false;
  const end = tagEnd(text, index);
  if (end < 0) return false;
  const tag = text.slice(index, end + 1);
  return /\bclass\s*=\s*["'][^"']*\btactic\b[^"']*["']/.test(tag);
}

function isTacticStateSpanOpen(text, index) {
  if (!text.startsWith("<span", index)) return false;
  const end = tagEnd(text, index);
  if (end < 0) return false;
  const tag = text.slice(index, end + 1);
  return /\bclass\s*=\s*["'][^"']*\btactic-state\b[^"']*["']/.test(tag);
}

function matchingSpanEnd(text, spanStart) {
  let depth = 0;
  let index = spanStart;

  while (index < text.length) {
    const nextOpen = text.indexOf("<span", index);
    const nextClose = text.indexOf("</span>", index);

    if (nextClose < 0) return -1;
    if (nextOpen >= 0 && nextOpen < nextClose) {
      const end = tagEnd(text, nextOpen);
      if (end < 0) return -1;
      depth += 1;
      index = end + 1;
    } else {
      depth -= 1;
      index = nextClose + "</span>".length;
      if (depth === 0) return index;
      if (depth < 0) return -1;
    }
  }

  return -1;
}

function rewriteTacticAt(text, start) {
  const outerOpenEnd = tagEnd(text, start);
  if (outerOpenEnd < 0) return null;

  let cursor = skipWhitespace(text, outerOpenEnd + 1);
  if (!text.startsWith("<label", cursor)) return null;

  const labelOpenEnd = tagEnd(text, cursor);
  if (labelOpenEnd < 0) return null;

  const labelCloseStart = text.indexOf("</label>", labelOpenEnd + 1);
  if (labelCloseStart < 0) return null;

  const labelInner = text.slice(labelOpenEnd + 1, labelCloseStart);
  cursor = skipWhitespace(text, labelCloseStart + "</label>".length);

  if (!text.startsWith("<input", cursor)) return null;
  const inputEnd = tagEnd(text, cursor);
  if (inputEnd < 0) return null;

  cursor = skipWhitespace(text, inputEnd + 1);
  if (!isTacticStateSpanOpen(text, cursor)) return null;

  const tacticStateEnd = matchingSpanEnd(text, cursor);
  if (tacticStateEnd < 0) return null;

  cursor = skipWhitespace(text, tacticStateEnd);
  if (!text.startsWith("</span>", cursor)) return null;

  return {
    end: cursor + "</span>".length,
    replacement: labelInner,
  };
}

function stripTacticStates(text) {
  let out = "";
  let cursor = 0;
  let removedBytes = 0;
  let tactics = 0;

  while (cursor < text.length) {
    const start = text.indexOf('<span class="tactic"', cursor);
    if (start < 0) break;

    if (!isTacticSpanOpen(text, start)) {
      out += text.slice(cursor, start + 1);
      cursor = start + 1;
      continue;
    }

    const rewritten = rewriteTacticAt(text, start);
    if (!rewritten) {
      out += text.slice(cursor, start + 1);
      cursor = start + 1;
      continue;
    }

    out += text.slice(cursor, start);
    out += rewritten.replacement;
    removedBytes += rewritten.end - start - rewritten.replacement.length;
    tactics += 1;
    cursor = rewritten.end;
  }

  if (cursor === 0) {
    return { text, removedBytes: 0, tactics: 0 };
  }

  out += text.slice(cursor);
  return { text: out, removedBytes, tactics };
}

function stripMetadata(text, opts) {
  let out = text;
  let removedBytes = 0;

  if (opts.stripBindings) {
    const before = out.length;
    out = out.replace(/\sdata-binding="[^"]*"/g, "");
    removedBytes += before - out.length;
  }

  if (opts.stripHovers) {
    const before = out.length;
    out = out.replace(/\sdata-verso-hover="[^"]*"/g, "");
    removedBytes += before - out.length;
  }

  return { text: out, removedBytes };
}

async function main() {
  const opts = parseArgs(process.argv.slice(2));
  const root = path.resolve(opts.siteDir);
  const rootStat = await stat(root);
  if (!rootStat.isDirectory()) {
    throw new Error(`SITE_DIR is not a directory: ${root}`);
  }

  let files = 0;
  let changedFiles = 0;
  let totalBefore = 0;
  let totalAfter = 0;
  let totalTactics = 0;
  let proofStateBytes = 0;
  let metadataBytes = 0;

  for await (const file of htmlFiles(root)) {
    files += 1;
    const before = await readFile(file, "utf8");
    totalBefore += Buffer.byteLength(before);

    const proofPass = stripTacticStates(before);
    const metadataPass = stripMetadata(proofPass.text, opts);
    const after = metadataPass.text;

    proofStateBytes += proofPass.removedBytes;
    metadataBytes += metadataPass.removedBytes;
    totalTactics += proofPass.tactics;
    totalAfter += Buffer.byteLength(after);

    if (after !== before) {
      await writeFile(file, after);
      changedFiles += 1;
    }
  }

  const saved = totalBefore - totalAfter;
  const pct = totalBefore === 0 ? 0 : (saved / totalBefore) * 100;
  const ratio = totalAfter === 0 ? "inf" : (totalBefore / totalAfter).toFixed(2);

  console.log(`Scanned ${files} HTML files under ${root}`);
  console.log(`Changed ${changedFiles} files`);
  console.log(`Removed ${totalTactics} inline tactic proof states`);
  console.log(`Saved ${proofStateBytes} bytes from proof states`);
  if (opts.stripBindings || opts.stripHovers) {
    console.log(`Saved ${metadataBytes} bytes from optional metadata stripping`);
  }
  console.log(`Before: ${totalBefore} bytes`);
  console.log(`After:  ${totalAfter} bytes`);
  console.log(`Saved:  ${saved} bytes (${pct.toFixed(1)}%, ${ratio}x smaller)`);
}

main().catch((err) => {
  console.error(`slim-literate-html: ${err.message}`);
  process.exit(1);
});
