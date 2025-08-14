import json, types
separator = "1498708047921580983"
_object_cache = []
mod = types.ModuleType("sandbox")
mod.__dict__.update(
    {"_object_cache": _object_cache}
)

while 1:
    res = ""
    try:
        inp = input()
        if inp == "":
            break
        inp = json.loads(inp)
        if inp["run_method"] == "exec":
            exec(str(inp["statement"]), mod.__dict__)
            res = '{"type": "NoneType", "value": "None"}'
        elif inp["run_method"] == "eval":
            res_val = eval(str(inp["statement"]), mod.__dict__)
            if str(type(res_val)) != "<class '" + inp["type"] + "'>" or inp["type"] == "object":
                if inp["type"] == "object":
                    res = f'{{"type": "object", "value": "_object_cache[' + str(len(_object_cache)) + ']"}'
                    _object_cache.append(res_val)
                else:
                    res = f'{{"type": "Error", "value": "Output of statement didn\'t match the expected type. Expected <class \'' + inp["type"] + f'\'>, got {type(res_val)}"}}'
            else:
                res = f'{{"type": "' + inp["type"] + f'", "value": ' + json.dumps(str(res_val)) + '}'
    except Exception as e:
        res = f'{{"type": "Error", "value": "{e}"}}'
    print(res + f'\n{separator}', flush=True)