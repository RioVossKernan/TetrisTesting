const stage = new Stage();
var cur_instance = 0;
var BoardSig = instances[cur_instance].signature('Board').atoms()[0]; // Get the board signature from Forge

//MANUALLY SET THESE VALUES
const grid_width = 5;
const grid_height = 5;

//NEXT STATE BUTTON
let next_button = new Rectangle({
    label: 'NEXT STATE: ' + `${cur_instance}`,
    labelColor: 'black',
    coords: {x: 100, y:10},
    color: 'orange',
    height: 30,
    width: 120,

    events: [
        {event: 'click', callback: () => {
            cur_instance++;
            if (cur_instance >= instances.length) {
                cur_instance = 0;
            }
            BoardSig = instances[cur_instance].signature('Board').atoms()[0];
            stage.render(svg, document);
        }}
    ]
}); 
stage.add(next_button);

function updateGrid() {
    //INITIALIZE GRID
    let tetrisGrid = new Grid({
        grid_location: {x: 50, y:50},
        cell_size: {x_size: 40, y_size: 40},
        grid_dimensions: {x_size: grid_width, y_size: grid_height}
    })

    //ADD VALUES TO GRID
    for (r = 0; r < grid_height; r++) {
        for (c = 0; c < grid_width; c++) {
            let value = BoardSig.values[r][c].toString().substring(0,1) // Get the value at this position as a string
            if (value === "F") {
                tetrisGrid.add({x: c, y: r}, new Rectangle({height: 40, width: 40, color: "green", borderColor: "black"}))
            }
        }
    }
    stage.add(tetrisGrid);
    stage.render(svg, document);
}

updateGrid();