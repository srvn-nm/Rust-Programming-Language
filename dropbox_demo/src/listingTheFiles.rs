use std::env;

// Import the dotenvy crate function to load the .env file
use dotenvy::dotenv; 

// Import necessary Dropbox SDK components
use dropbox_sdk::default_client::UserAuthDefaultClient;
use dropbox_sdk::files; 
use dropbox_sdk::oauth2::Authorization; 


fn listingFiles() -> Result<(), Box<dyn std::error::Error>> {
    // 1. Load the .env file
    // The .ok() ignores the error if the .env file isn't found (e.g., in production)
    dotenv().ok(); 

    // 2. Load credentials
    let app_key: String = env::var("DROPBOX_APP_KEY")
        .expect("Missing DROPBOX_APP_KEY in .env");
    let app_secret: String = env::var("DROPBOX_APP_SECRET")
        .expect("Missing DROPBOX_APP_SECRET in .env");
    let refresh_token: String = env::var("DROPBOX_REFRESH_TOKEN")
        .expect("Missing DROPBOX_REFRESH_TOKEN in .env");

    // 3. Initialize the Dropbox Client
    // The Authorization struct holds the token, which is what the client::new() function requires.
    let auth = Authorization::from_client_secret_refresh_token(
        app_key, 
        app_secret, 
        refresh_token
        );

    // 4. Initialize the Dropbox Client using the Authorization struct
    let client = UserAuthDefaultClient::new(auth);

    // 4. Test the connection by listing the root folder ("")
    println!("🔑 Successfully initialized Dropbox client. Requesting folder contents...");
    
    let result = files::list_folder(&client, &files::ListFolderArg::new("".to_owned()))?;

    // 5. Print the results
    println!("--- Dropbox Root Folder Contents ---");
    for entry in result.entries {
        match entry {
            files::Metadata::File(file) => {
                println!("📄 FILE: {}", file.path_display.unwrap_or_default());
            }
            files::Metadata::Folder(folder) => {
                println!("📂 FOLDER: {}", folder.path_display.unwrap_or_default());
            }
            _ => {} 
        }
    }
    
    println!("------------------------------------");

    Ok(())
}