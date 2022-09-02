// Run with Node.js

// const macroName = '{! solution !}';
const macroName = 'solution';
const maximumCaseDepth = 40;

/**
 * @param {number} depth 
 */
function makeCase(depth) {
    const name = "introTest" + depth;

    const parameters = 'ℕ → '.repeat(depth);
    const type = `${parameters}ℕ`;
    const declaration = `${name} : ${type}`;

    const definition = `${name} = ${macroName}`;

    const testCase = `${declaration}\n${definition}`;
    return testCase;
}

/** @type string[] */
const cases = [];

for (let i = 0; i <= maximumCaseDepth; ++i) {
    const testCase = makeCase(i);
    cases.push(testCase);
}

const output = cases.join('\n\n');
console.log(output);
