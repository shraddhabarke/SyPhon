function populateWordStems() {
  let csvRows = $.csv.toArrays(this.result);
  let tableBody = $('<tbody>');
  csvRows.forEach(csvRow => {
    let tableRow = $('<tr>');
    let underlyingForm = $('<td>').text(csvRow[0]);
    let realization = $('<td>').text(csvRow[1]);
    tableRow.append(underlyingForm).append(realization).appendTo(tableBody);
  });
  $('#word-stems > tbody').replaceWith(tableBody);
}

function renderRules(rules) {

  // ERSP: Deactivate Loading Notification
  document.getElementById("loading-screen-backdrop").style.display = "none";
  console.log("%c Loading-screen Backdrop Activated!", "background: beige; color: purple;");

  function renderPhone(phone) {
    let phoneString = '';

    if ($.type(phone) === 'string') {
      phoneString += phone;
    } else if (phone === null) {
      phoneString += '_';
    } else {
      phoneString += '[';
      phoneString += phone
	.map(feature => (feature.positive ? '+' : '-') + feature.feature)
	.join(' ');
      phoneString += ']';
    }

    return phoneString;
  }

  function renderRule(rule) {
    let target = renderPhone(rule.target);
    let change = renderPhone(rule.change);

    let context = '_';
    if (rule.context.left !== null) {
      let left = renderPhone(rule.context.left);
      context = `${left} ${context}`;
    }
    if (rule.context.right !== null) {
      let right = renderPhone(rule.context.right);
      context = `${context} ${right}`;
    }

    return `${target} → ${change} / ${context}`;
  }

  rulesElem = $('#rules');
  rulesElem.empty();
  rules
    .forEach(rule => {
    $('<li>').text(rule).appendTo(rulesElem);
  });
}

$('#csv-upload').change(function () {
  let file = this.files[0];
  let reader = new FileReader();
  reader.onload = populateWordStems;
  reader.readAsText(file);
});

// ERSP: Dropdown Menu for GitHub datasets HTML Element
$('#csv-upload-github').change(function () {
  console.log("%c Change of the HTML element 'csv-select-github'", "background: beige; color: purple;");
});


$('#infer').click(() => {

  // ERSP: Activate Loading Notification
  document.getElementById("loading-screen-backdrop").style.display = "initial";
  console.log("%c Loading-screen Backdrop Activated!", "background: beige; color: purple;");


  let wordStems = [];

  $('#word-stems > tbody > tr').each(function (row) {
    let data = $('td', this);
    wordStems.push({
      underlyingForm: $(data[0]).text(),
      realization: $(data[1]).text()
    });
  });

  let payload = {
    wordStems: wordStems
  };

  $.post({
    url: 'api/infer_rule',
    contentType: 'application/json',
    data: JSON.stringify(payload)
  })
    .then(renderRules)
    .catch(error => {
      console.log(error);
    });
})
