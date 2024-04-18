const stage = new Stage();
const BoardSig = instance.signature('Board').atoms()[0]; // Get the board signature from Forge
const grid_width = 9;
const grid_height = 9;

//INITIALIZE GRID
let sudokuGrid = new Grid({
    grid_location: {x: 50, y:50},
    cell_size: {x_size: 40, y_size: 40},
    grid_dimensions: {x_size: grid_width, y_size: grid_height}
})

//ADD CHUNK OUTLINES
for (r = 0; r < 3; r++) {
    for (c = 0; c < 3; c++) {
        let chunk = new Rectangle({
            height: 120,
            width: 120,
            borderWidth: 5,
            coords: {x: 50 + c * 120, y: 50 + r * 120},
            color: 'white',
            borderColor: "black",
        })
        stage.add(chunk)
    }
}

//ADD VALUES TO GRID
for (r = 0; r < grid_height; r++) {
    for (c = 0; c < grid_width; c++) {
        let value = BoardSig.values[r][c].toString().substring(0,1) // Get the value at this position as a string
        sudokuGrid.add({x: c, y: r}, new TextBox({text: `${value}`, fontSize: 26, color: "black"}))
    }
}
stage.add(sudokuGrid);

stage.render(svg, document);