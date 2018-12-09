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

function renderRule(rule) {
  function renderPhone(phone) {
    let phoneString = '';

    if ($.type(phone) === 'string') {
      phoneString += phone;
    } else if (phone.length === 0) {
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
  
  let ruleString =
      renderPhone(rule.phone) +
      ' → ' +
      renderPhone(rule.change) +
      ' / ' +
      renderPhone(rule.context.left) +
      ' _ ' +
      renderPhone(rule.context.right);

  $('#rule').text(ruleString);
}

$('#csv-upload').change(function () {
  let file = this.files[0];
  let reader = new FileReader();
  reader.onload = populateWordStems;
  reader.readAsText(file);
});

$('#infer').click(() => {
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
    .then(renderRule)
    .catch(error => {
      console.log(error);
    });
})
