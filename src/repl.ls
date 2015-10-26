_ = require \lodash

angular.module 'app', [\ui.codemirror, \ui.select]
  ..controller "Ctrl" ($scope) !->

    $scope.cmOptions = cmOptions()
    $scope.wrapper = (parent) ->
        submitCallback = (cm) ->
            calc = cm.parent
            thisIdx = _.findIndex($scope.history, (h) ->
                h.id == calc.id
            )
            calc.output = "Result of " + calc.input

            # add a new field if this is the last field or if the next one has been evaluated
            if (thisIdx == ($scope.history.length - 1) ||
                typeof $scope.history[thisIdx+1].output != \undefined)

                nextIdx = _.max($scope.history, (h) -> h.id).id + 1
                $scope.history.splice(thisIdx+1, 0,
                    {id: nextIdx, input: calc.output})
            else
                $scope.history[thisIdx+1].input = calc.output
            cm.getInputField().blur()
            $scope.$apply()

        loadCallback = (cm) ->
            cm.parent = parent

        initEditor(submitCallback, loadCallback)

    $scope.history = [
        {id: 1, input: "a b"}
    ]
    $scope.output = {}
    $scope.data = []