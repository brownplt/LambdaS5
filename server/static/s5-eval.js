$(function() {
  var codeBox = $(".codeinput");
  $('#send-code').on("click", function(e) {
    $.ajax({
      url: BASEURL + "/eval",
      type: "POST",
      dataType: "json",
      data: {
        code: codeBox.val()
      },
      success: function(data, status, xhr) {
        $("#eval-out").val(data['stdout-eval']);
        $("#desugar-out").val(data['stdout-dsg']);
        var errors = "===From parse/desugar===\n";
        errors += data['stderr-dsg'];
        errors += "\n\n===From eval===\n";
        errors += data['stderr-eval'];
        $("#errors").val(errors);
      },
      error: function(xhr, status, error) {
        console.log("[S5-Eval] An error occurred processing your request:", status, error);
      }
    });
  });
});
