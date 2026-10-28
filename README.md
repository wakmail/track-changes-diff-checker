# Track Changes Diff Checker

**Use it here:** https://wakmail.github.io/track-changes-diff-checker/

Compare two versions of a piece of writing and see what changed, marked up like tracked changes in Word or Google Docs. Deletions are red and struck through, additions are green.

Most diff checkers compare line by line, which falls apart when a paragraph gets rewritten. This one matches paragraphs first, then sentences within them, then diffs the words inside each matched sentence. Paragraphs that moved are still paired with their old versions, and sentences that changed too much show as a full deletion followed by the new sentence.

You can copy the result straight into Google Docs with the colors intact.

It all runs in the browser, so your text is never uploaded anywhere.

## Running it

Open `index.html` in a browser. There's no build step.
